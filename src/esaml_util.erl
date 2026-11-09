%% esaml - SAML for erlang
%%
%% Copyright (c) 2013, Alex Wilson and the University of Queensland
%% All rights reserved.
%%
%% Distributed subject to the terms of the 2-clause BSD license, see
%% the LICENSE file in the root of the distribution.

%% @doc Utility functions
-module(esaml_util).

-include_lib("xmerl/include/xmerl.hrl").
-include_lib("public_key/include/public_key.hrl").
-include("esaml.hrl").

-export([datetime_to_saml/1, saml_to_datetime/1]).
-export([start_ets/0, check_dupe_ets/2]).
-export([folduntil/3, thread/2, threaduntil/2]).
-export([build_nsinfo/2]).
-export([load_private_key/1, import_private_key/2]).
-export([load_certificate_chain/1, import_certificate_chain/2]).
-export([load_certificate/1, import_certificate/2]).
-export([load_metadata/2, load_metadata/1]).
-export([convert_fingerprints/1]).
-export([unique_id/0]).
-export([scan_untrusted_xml/1, bounded_inflate/1]).

%% Real IdP responses are 5-100 KB. Refuse any payload over 512 KB.
-define(MAX_XML_BYTES, 524288).

%% @doc Converts various ascii hex/base64 fingerprint formats to binary
-spec convert_fingerprints([string() | binary()]) -> [binary()].
convert_fingerprints(FPs) ->
    FPSources = FPs ++ esaml:config(trusted_fingerprints, []),
    lists:map(fun(Print) ->
        if is_list(Print) ->
            case string:tokens(Print, ":") of
                [Type, Base64] ->
                    Hash = base64:decode(Base64),
                    case string:to_lower(Type) of
                        "sha" -> {sha, Hash};
                        "sha1" -> {sha, Hash};
                        "md5" -> {md5, Hash};
                        "sha256" -> {sha256, Hash};
                        "sha384" -> {sha384, Hash};
                        "sha512" -> {sha512, Hash}
                    end;
                [_] -> error("unknown fingerprint format");
                HexParts ->
                    list_to_binary([list_to_integer(P, 16) || P <- HexParts])
            end;
        is_binary(Print) ->
            Print;
        true ->
            error("unknown fingerprint format")
        end
    end, FPSources).

%% @doc Converts a calendar:datetime() into SAML time string
-spec datetime_to_saml(calendar:datetime()) -> esaml:datetime().
datetime_to_saml(Time) ->
    {{Y,Mo,D}, {H, Mi, S}} = Time,
    lists:flatten(io_lib:format("~4.10.0B-~2.10.0B-~2.10.0BT~2.10.0B:~2.10.0B:~2.10.0BZ", [Y, Mo, D, H, Mi, S])).

%% @doc Converts a SAML time string into a calendar:datetime()
%%
%% Inverse of datetime_to_saml/1
-spec saml_to_datetime(esaml:datetime()) -> calendar:datetime().
saml_to_datetime(Stamp) ->
    StampBin = if is_list(Stamp) -> list_to_binary(Stamp); true -> Stamp end,
    <<YBin:4/binary, "-", MoBin:2/binary, "-", DBin:2/binary, "T",
        HBin:2/binary, ":", MiBin:2/binary, ":", SBin:2/binary, Rest/binary>> = StampBin,
    %% check that time in UTC timezone because we don't handle another timezones properly
    $Z = binary:last(Rest),
    F = fun(B) -> list_to_integer(binary_to_list(B)) end,
    {{F(YBin), F(MoBin), F(DBin)}, {F(HBin), F(MiBin), F(SBin)}}.

%% @private
-spec folduntil(F :: fun(), Acc :: term(), List :: []) -> AccOut :: term().
folduntil(_F, Acc, []) -> Acc;
folduntil(F, Acc, [Next | Rest]) ->
    case F(Next, Acc) of
        {stop, AccOut} -> AccOut;
        NextAcc -> folduntil(F, NextAcc, Rest)
    end.

%% @private
thread([], Acc) -> Acc;
thread([F | Rest], Acc) ->
    thread(Rest, F(Acc)).

%% @private
-spec threaduntil([fun((Acc :: term()) -> {error, term()} | {stop, term()} | term())], InitAcc::term()) -> {ok, term()} | {error, term()}.
threaduntil([], Acc) -> {ok, Acc};
threaduntil([F | Rest], Acc) ->
    case (catch F(Acc)) of
        {'EXIT', Reason} ->
            {error, Reason};
        {error, Reason} ->
            {error, Reason};
        {stop, LastAcc} ->
            {ok, LastAcc};
        NextAcc ->
            threaduntil(Rest, NextAcc)
    end.

%% @private
-spec build_nsinfo(#xmlNamespace{}, #xmlElement{}) -> #xmlElement{}.
build_nsinfo(Ns, Attr = #xmlAttribute{name = Name}) ->
    case string:tokens(atom_to_list(Name), ":") of
        [NsPrefix, Rest] -> Attr#xmlAttribute{namespace = Ns, nsinfo = {NsPrefix, Rest}};
        _ -> Attr#xmlAttribute{namespace = Ns}
    end;
build_nsinfo(Ns, Elem = #xmlElement{name = Name, content = Kids, attributes = Attrs}) ->
    Elem2 = case string:tokens(atom_to_list(Name), ":") of
        [NsPrefix, Rest] -> Elem#xmlElement{namespace = Ns, nsinfo = {NsPrefix, Rest}};
        _ -> Elem#xmlElement{namespace = Ns}
    end,
    Elem2#xmlElement{attributes = [build_nsinfo(Ns, Attr) || Attr <- Attrs],
                    content = [build_nsinfo(Ns, Kid) || Kid <- Kids]};
build_nsinfo(_Ns, Other) -> Other.

%% @private
start_ets() ->
    case erlang:whereis(esaml_ets_table_owner) of
        undefined ->
            create_tables();
        Pid ->
            Pid ! {self(), check_ready},
            receive
                {Pid, ready} -> {ok, Pid}
            end
    end.

%% @private
create_tables() ->
    Caller = self(),
    Pid = spawn_link(fun() ->
              register(esaml_ets_table_owner, self()),
              ets:new(esaml_assertion_seen, [set, public, named_table]),
              ets:new(esaml_privkey_cache, [set, public, named_table]),
              ets:new(esaml_certbin_cache, [set, public, named_table]),
              ets:new(esaml_idp_meta_cache, [set, public, named_table]),
              Caller ! {self(), ready},
              ets_table_owner()
         end),

    receive
        {Pid, ready} -> ok
    end,

    {ok, Pid}.

%% @private
ets_table_owner() ->
    receive
        stop ->
            ok;
        {Caller, check_ready} ->
            Caller ! {self(), ready},
            ets_table_owner();
        _ ->
            ets_table_owner()
    end.

%% @doc Loads a private key from a file on disk (or ETS memory cache)
-spec load_private_key(Path :: string()) -> #'RSAPrivateKey'{}.
load_private_key(Path) ->
    case ets:lookup(esaml_privkey_cache, Path) of
        [{_, Key}] ->
            Key;
        _ ->
            {ok, KeyFile} = file:read_file(Path),
            do_import_private_key(KeyFile, Path)
    end.

-spec import_private_key(EncodedKey :: string(), Identifier :: term()) -> #'RSAPrivateKey'{}.
import_private_key(EncodedKey, Identifier) ->
    case ets:lookup(esaml_privkey_cache, Identifier) of
        [{_, Key}] -> Key;
        _ -> do_import_private_key(EncodedKey, Identifier)
    end.

do_import_private_key(EncodedKey, Identifier) ->
    [KeyEntry] = public_key:pem_decode(EncodedKey),
    Key = case public_key:pem_entry_decode(KeyEntry) of
              #'PrivateKeyInfo'{privateKey = KeyData} ->
                  KeyDataBin = if is_list(KeyData) -> list_to_binary(KeyData);
                                  true -> KeyData
                               end,
                  public_key:der_decode('RSAPrivateKey', KeyDataBin);
              Other -> Other
          end,
    ets:insert(esaml_privkey_cache, {Identifier, Key}),
    Key.

-spec load_certificate(Path :: string()) -> binary().
load_certificate(Path) ->
    [CertBin] = load_certificate_chain(Path),
    CertBin.

-spec import_certificate(EncodedCert :: string(), Identifier :: term()) -> binary().
import_certificate(EncodedCert, Identifier) ->
    [CertBin] = import_certificate_chain(EncodedCert, Identifier),
    CertBin.

%% @doc Loads certificate chain from a file on disk (or ETS memory cache)
-spec load_certificate_chain(Path :: string()) -> [binary()].
load_certificate_chain(Path) ->
    case ets:lookup(esaml_certbin_cache, Path) of
        [{_, CertChain}] ->
            CertChain;
        _ ->
            {ok, EncodedCert} = file:read_file(Path),
            do_import_certificate_chain(EncodedCert, Path)
    end.

%% @doc Loads certificate chain from a file on disk (or ETS memory cache)
-spec import_certificate_chain(EncodedCerts :: string(), Identifier :: string()) -> [binary()].
import_certificate_chain(EncodedCerts, Identifier) ->
    case ets:lookup(esaml_certbin_cache, Identifier) of
        [{_, CertChain}] ->
            CertChain;
        _ ->
            do_import_certificate_chain(EncodedCerts, Identifier)
    end.

do_import_certificate_chain(EncodedCerts, Identifier) ->
    CertChain = [CertBin || {'Certificate', CertBin, not_encrypted} <- public_key:pem_decode(EncodedCerts)],
    ets:insert(esaml_certbin_cache, {Identifier, CertChain}),
    CertChain.

%% @doc Reads IDP metadata from a URL (or ETS memory cache) and validates the signature
-spec load_metadata(Url :: string(), Fingerprints :: [string() | binary()]) -> esaml:idp_metadata().
load_metadata(Url, FPs) ->
    Fingerprints = convert_fingerprints(FPs),
    case ets:lookup(esaml_idp_meta_cache, Url) of
        [{Url, Meta}] -> Meta;
        _ ->
            {ok, {{_Ver, 200, _}, _Headers, Body}} = httpc:request(get, {Url, []}, [{autoredirect, true}, {timeout, 3000}], []),
            {Xml, _} = xmerl_scan:string(Body, [{namespace_conformant, true}]),
            case xmerl_dsig:verify(Xml, Fingerprints) of
                ok -> ok;
                Err -> error(Err)
            end,
            {ok, Meta = #esaml_idp_metadata{}} = esaml:decode_idp_metadata(Xml),
            ets:insert(esaml_idp_meta_cache, {Url, Meta}),
            Meta
    end.

%% @doc Reads IDP metadata from a URL (or ETS memory cache)
-spec load_metadata(Url :: string()) -> esaml:idp_metadata().
load_metadata(Url) ->
    case ets:lookup(esaml_idp_meta_cache, Url) of
        [{Url, Meta}] -> Meta;
        _ ->
            Timeout = application:get_env(esaml, load_metadata_timeout, 15000),
            {ok, {{_Ver, 200, _}, _Headers, Body}} = httpc:request(get, {Url, []}, [{autoredirect, true}, {timeout, Timeout}], []),
            {Xml, _} = xmerl_scan:string(Body, [{namespace_conformant, true}]),
            {ok, Meta = #esaml_idp_metadata{}} = esaml:decode_idp_metadata(Xml),
            ets:insert(esaml_idp_meta_cache, {Url, Meta}),
            Meta
    end.

%% @doc Checks for a duplicate assertion using ETS tables in memory on all available nodes.
%%
%% This is a helper to be used as a DuplicateFun with esaml_sp:validate_assertion/3.
%% If you aren't using standard erlang distribution for your app, you probably don't
%% want to use this.
-spec check_dupe_ets(esaml:assertion(), Digest :: binary()) -> ok | {error, duplicate_assertion}.
check_dupe_ets(A, Digest) ->
    Now = erlang:localtime_to_universaltime(erlang:localtime()),
    NowSecs = calendar:datetime_to_gregorian_seconds(Now),
    DeathSecs = esaml:stale_time(A),
    {ResL, _BadNodes} = rpc:multicall(erlang, apply, [fun() ->
        case (catch ets:lookup(esaml_assertion_seen, Digest)) of
            [{Digest, seen} | _] -> seen;
            _ -> ok
        end
    end, []]),
    case lists:member(seen, ResL) of
        true ->
            {error, duplicate_assertion};
        _ ->
            Until = DeathSecs - NowSecs + 1,
            rpc:multicall(erlang, apply, [fun() ->
                case ets:info(esaml_assertion_seen) of
                    undefined ->
                        Me = self(),
                        Pid = spawn(fun() ->
                            register(esaml_ets_table_owner, self()),
                            ets:new(esaml_assertion_seen, [set, public, named_table]),
                            ets:new(esaml_privkey_cache, [set, public, named_table]),
                            ets:new(esaml_certbin_cache, [set, public, named_table]),
                            ets:insert(esaml_assertion_seen, {Digest, seen}),
                            Me ! {self(), ping},
                            ets_table_owner()
                        end),
                        receive
                            {Pid, ping} -> ok
                        end;
                    _ ->
                        ets:insert(esaml_assertion_seen, {Digest, seen})
                end,
                {ok, _} = timer:apply_after(Until * 1000, erlang, apply, [fun() ->
                    ets:delete(esaml_assertion_seen, Digest)
                end, []])
            end, []]),
            ok
    end.

% TODO: switch to uuid_erl hex pkg
unique_id() ->
    "id"
      ++ integer_to_list(erlang:system_time())
      ++ integer_to_list(erlang:unique_integer([positive])).

%% @doc Parse an untrusted SAML payload with xmerl.
%%
%% Refuse the payload before xmerl reads it when it is over 512 KB,
%% when it holds a NUL byte (UTF-16 or UCS-4 can hide a DOCTYPE),
%% when it holds a DOCTYPE, or when xmerl would make a new atom from it.
-spec scan_untrusted_xml(binary()) ->
    {ok, #xmlElement{}} |
    {error, payload_too_large | encoding_not_allowed | doctype_not_allowed |
            processing_instruction_not_allowed | unknown_xml_name | {bad_xml, term()}}.
scan_untrusted_xml(Xml) when is_binary(Xml) ->
    case check_untrusted_xml(Xml) of
        ok ->
            case check_names(Xml) of
                ok -> scan_xml(Xml);
                {error, _} = Error -> Error
            end;
        {error, _} = Error ->
            Error
    end.

%% xmerl_scan makes an atom from each element and attribute name, each local
%% name, each namespace URI and the declared encoding. Atoms are never freed,
%% so a stream of unsigned posts with new names fills the atom table and stops
%% the node. An untrusted payload may only use names that are atoms already.
%% vocabulary/0 makes the SAML, XML-DSig and XML-Enc names into atoms once.
%% The SAX parser reads names as strings, so this check makes no atoms.
check_names(Xml) ->
    ok = ensure_vocabulary(),
    case check_encoding(Xml) of
        ok ->
            Opts = [{event_fun, fun name_event/3}, {event_state, ok}],
            try xmerl_sax_parser:stream(Xml, Opts) of
                {ok, ok, _Rest} -> ok;
                %% The parser returns a {Tag, Reason} throw from name_event/3 with Tag first.
                {refuse, _Loc, Reason, _EndTags, _State} -> {error, Reason};
                {_Tag, _Loc, Reason, _EndTags, _State} -> {error, {bad_xml, Reason}};
                {_Tag, Reason} -> {error, {bad_xml, Reason}}
            catch
                throw:{refuse, Reason} -> {error, Reason};
                _:Reason -> {error, {bad_xml, Reason}}
            end;
        {error, _} = Error ->
            Error
    end.

%% xmerl_scan makes an atom from the encoding name in the XML declaration.
%% SAML bindings use UTF-8, so only that encoding is accepted.
check_encoding(Xml) ->
    Re = <<"\\A(?:\\xEF\\xBB\\xBF)?\\s*<\\?xml\\s[^>]*?\\bencoding\\s*=\\s*[\"']([^\"']*)[\"']">>,
    case re:run(Xml, Re, [{capture, all_but_first, list}]) of
        nomatch -> ok;
        {match, [Encoding]} ->
            case string:lowercase(Encoding) of
                "utf-8" -> require_atoms([Encoding]);
                _ -> {error, encoding_not_allowed}
            end
    end.

name_event({startPrefixMapping, Prefix, Uri}, _Loc, State) ->
    ok = require_atoms_or_throw([Prefix, Uri, qname("xmlns", Prefix)]),
    State;
name_event({startElement, Uri, Local, {Prefix, Local}, Attributes}, _Loc, State) ->
    ok = require_atoms_or_throw([Uri, Local, qname(Prefix, Local)]),
    lists:foreach(fun({AttrUri, AttrPrefix, AttrLocal, _Value}) ->
        ok = require_atoms_or_throw([AttrUri, AttrLocal, qname(AttrPrefix, AttrLocal)])
    end, Attributes),
    State;
name_event({processingInstruction, _Target, _Data}, _Loc, _State) ->
    throw({refuse, processing_instruction_not_allowed});
name_event(_Event, _Loc, State) ->
    State.

qname("", Local) -> Local;
qname(Prefix, "") -> Prefix;
qname(Prefix, Local) -> Prefix ++ ":" ++ Local.

require_atoms_or_throw(Names) ->
    case require_atoms(Names) of
        ok -> ok;
        {error, Reason} -> throw({refuse, Reason})
    end.

require_atoms(Names) ->
    try
        lists:foreach(fun(Name) -> _ = list_to_existing_atom(Name) end, Names)
    catch
        error:badarg -> {error, unknown_xml_name}
    end.

ensure_vocabulary() ->
    case persistent_term:get({?MODULE, vocabulary}, false) of
        true ->
            ok;
        false ->
            lists:foreach(fun(Name) -> _ = list_to_atom(Name) end, vocabulary()),
            persistent_term:put({?MODULE, vocabulary}, true)
    end.

%% The names that real IdP messages use. Each prefix is combined with each
%% local name, so an IdP may pick any of these prefixes.
vocabulary() ->
    Prefixes = ["saml", "saml2", "samlp", "saml2p", "ds", "dsig", "xenc", "xenc11", "xs",
                "xsd", "xsi", "ec", "md", "xml", "xmlns"]
               ++ ["ns" ++ integer_to_list(N) || N <- lists:seq(0, 9)],
    Namespaces = ["urn:oasis:names:tc:SAML:2.0:protocol",
                  "urn:oasis:names:tc:SAML:2.0:assertion",
                  "urn:oasis:names:tc:SAML:2.0:metadata",
                  "http://www.w3.org/2000/09/xmldsig#",
                  "http://www.w3.org/2001/04/xmldsig-more#",
                  "http://www.w3.org/2001/04/xmlenc#",
                  "http://www.w3.org/2009/xmlenc11#",
                  "http://www.w3.org/2001/10/xml-exc-c14n#",
                  "http://www.w3.org/2001/XMLSchema",
                  "http://www.w3.org/2001/XMLSchema-instance",
                  "http://www.w3.org/XML/1998/namespace",
                  "http://www.w3.org/2000/xmlns/"],
    Locals = string:lexemes(
        "AuthnRequest Response LogoutRequest LogoutResponse Status StatusCode StatusMessage "
        "StatusDetail Extensions NameIDPolicy RequestedAuthnContext Scoping IDPList IDPEntry "
        "GetComplete RequesterID SessionIndex ArtifactResolve ArtifactResponse Artifact "
        "AttributeQuery AuthnQuery AuthzDecisionQuery SubjectQuery AssertionIDRequest "
        "ManageNameIDRequest ManageNameIDResponse NewID NewEncryptedID Terminate "
        "NameIDMappingRequest NameIDMappingResponse RespondTo "
        "Assertion EncryptedAssertion Issuer Subject NameID BaseID EncryptedID SubjectConfirmation "
        "SubjectConfirmationData Conditions Condition AudienceRestriction Audience OneTimeUse "
        "ProxyRestriction Advice AssertionIDRef AssertionURIRef Statement AuthnStatement "
        "SubjectLocality AuthnContext AuthnContextClassRef AuthnContextDeclRef AuthnContextDecl "
        "AuthenticatingAuthority AttributeStatement Attribute AttributeValue EncryptedAttribute "
        "AuthzDecisionStatement Action Evidence "
        "Signature SignedInfo CanonicalizationMethod SignatureMethod Reference Transforms Transform "
        "DigestMethod DigestValue SignatureValue KeyInfo KeyName KeyValue RSAKeyValue Modulus "
        "Exponent DSAKeyValue X509Data X509Certificate X509IssuerSerial X509IssuerName "
        "X509SerialNumber X509SubjectName X509SKI X509CRL RetrievalMethod Object Manifest "
        "SignatureProperties SignatureProperty HMACOutputLength XPath PGPData SPKIData MgmtData "
        "InclusiveNamespaces "
        "EncryptedData EncryptedKey EncryptionMethod CipherData CipherValue CipherReference KeySize "
        "OAEPparams MGF ReferenceList DataReference KeyReference CarriedKeyName AgreementMethod "
        "EncryptionProperties EncryptionProperty "
        "ID Id Version IssueInstant Destination Consent InResponseTo Format NameQualifier "
        "SPNameQualifier SPProvidedID Method NotBefore NotOnOrAfter Recipient Address AuthnInstant "
        "SessionNotOnOrAfter Name NameFormat FriendlyName Value Algorithm URI Type MimeType Encoding "
        "PrefixList AllowCreate ForceAuthn IsPassive ProtocolBinding AssertionConsumerServiceURL "
        "AssertionConsumerServiceIndex AttributeConsumingServiceIndex ProviderName Reason "
        "Comparison ProxyCount Loc DNSName Resource Decision Namespace Count ProviderID "
        "type nil lang space base", " "),
    Names = Locals ++ Prefixes,
    ["", "xmlns", "UTF-8", "utf-8"] ++ Namespaces ++ Names
        ++ [P ++ ":" ++ N || P <- Prefixes, N <- Names].

check_untrusted_xml(Xml) when byte_size(Xml) > ?MAX_XML_BYTES ->
    {error, payload_too_large};
check_untrusted_xml(Xml) ->
    case binary:match(Xml, <<0>>) of
        nomatch ->
            case re:run(Xml, <<"<!DOCTYPE">>, [caseless, {capture, none}]) of
                nomatch -> ok;
                match -> {error, doctype_not_allowed}
            end;
        _ ->
            {error, encoding_not_allowed}
    end.

%% xmerl options: no entity declarations, no external reads.
%% The allow_entities option needs an xmerl that knows it (OTP 27.3.4.19 does).
scan_xml(Xml) ->
    Opts = [{namespace_conformant, true},
            {allow_entities, false},
            {fetch_fun, fun refuse_fetch/2}],
    try xmerl_scan:string(binary_to_list(Xml), Opts) of
        {Doc, _Rest} -> {ok, Doc}
    catch
        exit:{fatal, Reason} -> {error, {bad_xml, Reason}}
    end.

refuse_fetch(_Spec, _State) ->
    {error, external_fetch_not_allowed}.

%% @doc Inflate raw DEFLATE data with a 512 KB limit.
%%
%% Refuse input that is over 512 KB before inflation starts.
%% Stop the inflation when the output passes 512 KB.
%% Raise error:data_error on data that is not raw DEFLATE, as zlib:unzip/1 does.
-spec bounded_inflate(binary()) -> {ok, binary()} | {error, payload_too_large}.
bounded_inflate(Data) when byte_size(Data) > ?MAX_XML_BYTES ->
    {error, payload_too_large};
bounded_inflate(Data) ->
    Z = zlib:open(),
    try
        ok = zlib:inflateInit(Z, -15),
        inflate_loop(Z, zlib:safeInflate(Z, Data), [], 0)
    after
        zlib:close(Z)
    end.

inflate_loop(Z, {continue, Out}, Acc, Size0) ->
    Size = Size0 + iolist_size(Out),
    case Size > ?MAX_XML_BYTES of
        true -> {error, payload_too_large};
        false -> inflate_loop(Z, zlib:safeInflate(Z, []), [Acc, Out], Size)
    end;
inflate_loop(Z, {finished, Out}, Acc, Size0) ->
    case Size0 + iolist_size(Out) > ?MAX_XML_BYTES of
        true -> {error, payload_too_large};
        false ->
            %% inflateEnd/1 raises data_error on a truncated stream.
            ok = zlib:inflateEnd(Z),
            {ok, iolist_to_binary([Acc, Out])}
    end;
inflate_loop(_Z, {need_dictionary, _, _}, _Acc, _Size) ->
    erlang:error(data_error).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

fingerprints_test() ->
    [<<0:128>>] = convert_fingerprints([<<0:128>>]),
    {'EXIT', _} = (catch convert_fingerprints(["testing"])),
    [<<0:32,1,10,3>>] = convert_fingerprints(["00:00:00:00:01:0a:03"]),
    Hash = crypto:hash(sha, <<"testing1234">>),
    [{sha,Hash}] = convert_fingerprints(["SHA:" ++ base64:encode_to_string(Hash)]),
    Sha256 = crypto:hash(sha256, <<"testing1234">>),
    [{sha256,Sha256},{md5,Hash}] = convert_fingerprints(["SHA256:" ++ base64:encode_to_string(Sha256), "md5:" ++ base64:encode_to_string(Hash)]),
    {'EXIT', _} = (catch convert_fingerprints(["SOMEALGO:AAAAA="])).

datetime_test() ->
    "2013-05-02T17:26:53Z" = datetime_to_saml({{2013,5,2},{17,26,53}}),
    {{1990,11,23},{18,1,1}} = saml_to_datetime("1990-11-23T18:01:01Z").

build_nsinfo_test() ->
    EmptyNs = #xmlNamespace{},
    FooNs = #xmlNamespace{nodes = [{"foo", 'urn:foo:'}]},

    E1 = #xmlElement{name = 'foo', content = [#xmlText{value = 'bar'}]},
    E1 = build_nsinfo(EmptyNs, E1),

    E2 = #xmlElement{name = 'foo:Blah', content = [#xmlText{value = 'bar'}]},
    E2Ns = E2#xmlElement{nsinfo = {"foo", "Blah"}, namespace = FooNs},
    E2Ns = build_nsinfo(FooNs, E2),

    E3 = #xmlElement{name = 'blah:George', content = [E2]},
    E3Ns = E3#xmlElement{nsinfo = {"blah", "George"}, namespace = FooNs, content = [E2Ns]},
    E3Ns = build_nsinfo(FooNs, E3).

key_load_test() ->
    start_ets(),
    KeyPath = "test/selfsigned_key.pem",
    Key = load_private_key(KeyPath),
    ?assertEqual([{KeyPath, Key}], ets:lookup(esaml_privkey_cache, KeyPath)).

key_import_test() ->
    start_ets(),
    {ok, EncodedKey} = file:read_file("test/selfsigned_key.pem"),
    Key = import_private_key(EncodedKey, my_key),
    ?assertEqual([{my_key, Key}], ets:lookup(esaml_privkey_cache, my_key)).

bad_key_load_test() ->
    start_ets(),
    KeyPath = "test/bad_data.pem",
    ?assertException(error, {badmatch, []}, load_private_key(KeyPath)),
    ?assertEqual([], ets:lookup(esaml_privkey_cache, KeyPath)).

cert_load_test() ->
    start_ets(),
    CertPath = "test/selfsigned.pem",
    Cert = load_certificate(CertPath),
    ?assertEqual([{CertPath, [Cert]}], ets:lookup(esaml_certbin_cache, CertPath)).

cert_import_test() ->
    start_ets(),
    {ok, EncodedCert} = file:read_file("test/selfsigned.pem"),
    Cert = import_certificate(EncodedCert, my_cert),
    ?assertEqual([{my_cert, [Cert]}], ets:lookup(esaml_certbin_cache, my_cert)).

bad_cert_load_test() ->
    start_ets(),
    CertPath = "test/bad_data.pem",
    ?assertException(error, {badmatch, []}, load_certificate(CertPath)),
    ?assertEqual([{CertPath, []}], ets:lookup(esaml_certbin_cache, CertPath)).

-include("xmerl_xpath_macros.hrl").

-record(b, {name, ctext}).

xpath_attr_test() ->
    {Xml, _} = xmerl_scan:string("<a><b name=\"foo\"><c name=\"bar\">hi</c></b><b name=\"foobar\"><c name=\"foofoo\"></c></b></a>", [{namespace_conformant, true}]),
    Ns = [],
    Fun = ?xpath_attr("/a/b[@name='foo']/c/@name", b, name),
    Rec = Fun(#b{}),
    ?assertMatch(#b{name = "bar"}, Rec),
    Fun2 = ?xpath_attr("/a/b[@name='foobar']/c/@name", b, name),
    Rec2 = Fun2(Rec),
    ?assertMatch(#b{name = "foofoo"}, Rec2),
    Fun3 = ?xpath_attr("/a/b[@name='bar']/c/@name", b, name),
    Rec3 = Fun3(Rec2),
    ?assertMatch(Rec2, Rec3).

xpath_attr_trans_test() ->
    {Xml, _} = xmerl_scan:string("<a><b name=\"foo\"><c name=\"bar\">hi</c></b><b name=\"foobar\"><c name=\"foofoo\"></c></b></a>", [{namespace_conformant, true}]),
    Ns = [],
    Fun = ?xpath_attr("/a/b[@name='foobar']/c/@name", b, name, fun(X) -> list_to_atom(X) end),
    Rec = Fun(#b{}),
    ?assertMatch(#b{name = foofoo}, Rec).

xpath_text_test() ->
    {Xml, _} = xmerl_scan:string("<a><b name=\"foo\"><c name=\"bar\">hi</c></b><b name=\"foobar\"><c name=\"foofoo\"></c></b></a>", [{namespace_conformant, true}]),
    Ns = [],
    Fun = ?xpath_text("/a/b[@name='foo']/c/text()", b, ctext),
    Rec = Fun(#b{}),
    ?assertMatch(#b{ctext = "hi"}, Rec),
    Fun2 = ?xpath_text("/a/b[@name='foobar']/c/text()", b, ctext),
    Rec2 = Fun2(Rec),
    ?assertMatch(Rec, Rec2),
    Fun3 = ?xpath_text("/a/b[@name='bar']/c/text()", b, name),
    Rec3 = Fun3(Rec2),
    ?assertMatch(Rec2, Rec3).


scan_untrusted_xml_accepts_valid_test() ->
    Xml = <<"<samlp:Response xmlns:samlp=\"urn:oasis:names:tc:SAML:2.0:protocol\" Version=\"2.0\"/>">>,
    ?assertMatch({ok, #xmlElement{name = 'samlp:Response'}}, scan_untrusted_xml(Xml)).

scan_untrusted_xml_refuses_doctype_test() ->
    ?assertEqual({error, doctype_not_allowed}, scan_untrusted_xml(<<"<!DOCTYPE r><r/>">>)),
    ?assertEqual({error, doctype_not_allowed}, scan_untrusted_xml(<<"<!doctype r><r/>">>)),
    ?assertEqual({error, doctype_not_allowed}, scan_untrusted_xml(<<"<r><!-- <!DOCTYPE r> --></r>">>)).

scan_untrusted_xml_size_limit_test_() ->
    {timeout, 60, fun() ->
        Open = <<"<r>">>,
        Close = <<"</r>">>,
        Pad = 524288 - byte_size(Open) - byte_size(Close),
        Max = <<Open/binary, (binary:copy(<<"a">>, Pad))/binary, Close/binary>>,
        Over = <<Open/binary, (binary:copy(<<"a">>, Pad + 1))/binary, Close/binary>>,
        ?assertEqual(524288, byte_size(Max)),
        ?assertMatch({ok, #xmlElement{name = r}}, scan_untrusted_xml(Max)),
        ?assertEqual({error, payload_too_large}, scan_untrusted_xml(Over))
    end}.

scan_untrusted_xml_refuses_nul_test() ->
    Doc = <<"<!DOCTYPE r SYSTEM \"/nonexistent/esaml-test.dtd\"><r/>">>,
    Utf16 = <<16#FE, 16#FF, (unicode:characters_to_binary(Doc, utf8, {utf16, big}))/binary>>,
    ?assertEqual({error, encoding_not_allowed}, scan_untrusted_xml(Utf16)).

scan_options_refuse_entities_test() ->
    Xml = <<"<!DOCTYPE r [<!ENTITY x SYSTEM \"file:///etc/hosts\">]><r>&x;</r>">>,
    ?assertMatch({error, {bad_xml, {{error, entities_not_allowed}, _, _, _}}}, scan_xml(Xml)).

scan_options_refuse_external_dtd_test() ->
    Xml = <<"<!DOCTYPE r SYSTEM \"/nonexistent/esaml-test.dtd\"><r/>">>,
    ?assertMatch({error, {bad_xml, {{error_fetching_DTD, _}, _, _, _}}}, scan_xml(Xml)).

bounded_inflate_test() ->
    ?assertEqual({ok, <<"<r/>">>}, bounded_inflate(zlib:zip(<<"<r/>">>))),
    Big = <<"<r>", (binary:copy(<<"a">>, 2 * 1024 * 1024))/binary, "</r>">>,
    ?assertEqual({error, payload_too_large}, bounded_inflate(zlib:zip(Big))),
    ?assertError(data_error, bounded_inflate(<<"<r/>">>)),
    %% Input over 512 KB that inflates to a small document.
    ?assertEqual({error, payload_too_large},
                 bounded_inflate(<<(empty_stored_blocks(110000))/binary,
                                   (zlib:zip(<<"<r/>">>))/binary>>)),
    %% The inflation stops at the limit and never reads the bad data after it.
    ?assertEqual({error, payload_too_large},
                 bounded_inflate(<<(deflate_sync(Big))/binary, 16#FF, 16#FF>>)).

%% Non-final stored DEFLATE blocks of length 0, 5 bytes each.
empty_stored_blocks(N) ->
    binary:copy(<<0, 0, 0, 16#FF, 16#FF>>, N).

%% A raw DEFLATE stream with no final block. Data can follow it.
deflate_sync(Data) ->
    Z = zlib:open(),
    ok = zlib:deflateInit(Z, default, deflated, -15, 8, default),
    Out = iolist_to_binary(zlib:deflate(Z, Data, sync)),
    zlib:close(Z),
    Out.

%% A fresh name in each place where xmerl_scan makes an atom.
fresh_name() ->
    "esamlfresh" ++ integer_to_list(erlang:unique_integer([positive])).

fresh_name_docs() ->
    [N1, N2, N3, N4, N5] = [fresh_name() || _ <- lists:seq(1, 5)],
    [list_to_binary(D) || D <- [
        "<" ++ N1 ++ "/>",
        "<saml:" ++ N1 ++ " xmlns:saml=\"urn:oasis:names:tc:SAML:2.0:assertion\"/>",
        "<" ++ N2 ++ ":Response xmlns:" ++ N2 ++ "=\"urn:oasis:names:tc:SAML:2.0:protocol\"/>",
        "<Response xmlns=\"urn:" ++ N3 ++ "\"/>",
        "<Response " ++ N4 ++ "=\"x\"/>",
        "<Response xmlns:saml=\"urn:oasis:names:tc:SAML:2.0:assertion\" saml:" ++ N4 ++ "=\"x\"/>",
        "<?xml version=\"1.0\" encoding=\"" ++ N5 ++ "\"?><Response/>",
        "<Response><?" ++ N5 ++ " data?></Response>"
    ]].

scan_untrusted_xml_makes_no_new_atoms_test() ->
    %% Load the parser modules first, so loading them does not count.
    {ok, _} = scan_untrusted_xml(<<"<Response/>">>),
    Docs = fresh_name_docs(),
    Before = erlang:system_info(atom_count),
    Results = [scan_untrusted_xml(D) || D <- Docs],
    ?assertEqual(Before, erlang:system_info(atom_count)),
    lists:foreach(fun({D, R}) -> ?assertMatch({{error, _}, _}, {R, D}) end,
                  lists:zip(Docs, Results)).

scan_untrusted_xml_refuses_unknown_names_test() ->
    ?assertEqual({error, unknown_xml_name},
                 scan_untrusted_xml(list_to_binary("<" ++ fresh_name() ++ "/>"))),
    ?assertEqual({error, processing_instruction_not_allowed},
                 scan_untrusted_xml(<<"<Response><?xml-stylesheet href=\"a\"?></Response>">>)),
    ?assertEqual({error, encoding_not_allowed},
                 scan_untrusted_xml(<<"<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?><Response/>">>)),
    ?assertMatch({ok, #xmlElement{name = 'Response'}},
                 scan_untrusted_xml(<<"<?xml version=\"1.0\" encoding=\"UTF-8\"?><Response/>">>)).

scan_untrusted_xml_accepts_real_idp_responses_test() ->
    Paths = filelib:wildcard("test/idp_responses/*.xml"),
    ?assertEqual(6, length(Paths)),
    lists:foreach(fun(Path) ->
        {ok, Xml} = file:read_file(Path),
        ?assertMatch({{ok, #xmlElement{}}, _}, {scan_untrusted_xml(Xml), Path})
    end, Paths).

-endif.
