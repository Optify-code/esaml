%% esaml - SAML for erlang
%%
%% Copyright (c) 2013, Alex Wilson and the University of Queensland
%% All rights reserved.
%%
%% Distributed subject to the terms of the 2-clause BSD license, see
%% the LICENSE file in the root of the distribution.

%% @doc SAML HTTP binding handlers
-module(esaml_binding).

-export([decode_response/2, encode_http_redirect/4, encode_http_post/3, encode_http_post/4]).

-include_lib("xmerl/include/xmerl.hrl").
-define(deflate, <<"urn:oasis:names:tc:SAML:2.0:bindings:URL-Encoding:DEFLATE">>).

-type uri() :: binary() | string().
-type html_doc() :: binary().
-type xml() :: #xmlElement{} | #xmlDocument{}.

%% @private
-spec xml_payload_type(xml()) -> binary().
xml_payload_type(Xml) ->
    case Xml of
        #xmlDocument{content = [#xmlElement{name = Atom}]} ->
            case lists:suffix("Response", atom_to_list(Atom)) of
                true -> <<"SAMLResponse">>;
                _ -> <<"SAMLRequest">>
            end;
        #xmlElement{name = Atom} ->
            case lists:suffix("Response", atom_to_list(Atom)) of
                true -> <<"SAMLResponse">>;
                _ -> <<"SAMLRequest">>
            end;
        _ -> <<"SAMLRequest">>
    end.

%% @doc Unpack and parse a SAMLResponse with given encoding.
%%
%% Returns {error, Reason} when the payload is refused. The payload is refused
%% when it is over 512 KB (before or after inflation), holds a NUL byte, or
%% holds a DOCTYPE. Invalid base64 or invalid DEFLATE data still raise an error.
-spec decode_response(SAMLEncoding :: binary(), SAMLResponse :: binary()) -> xml() | {error, term()}.
decode_response(?deflate, SAMLResponse) ->
    case esaml_util:bounded_inflate(base64:decode(SAMLResponse)) of
        {ok, XmlData} -> scan_payload(XmlData);
        {error, _} = Error -> Error
    end;
decode_response(_, SAMLResponse) ->
    Data = base64:decode(SAMLResponse),
    case (catch esaml_util:bounded_inflate(Data)) of
        {ok, XmlData} -> scan_payload(XmlData);
        %% Too large after inflation: do not fall back to the raw data.
        {error, _} = Error -> Error;
        %% Not DEFLATE data: parse it as raw XML, as before.
        {'EXIT', _} -> scan_payload(Data)
    end.

%% @private
scan_payload(XmlData) ->
    case esaml_util:scan_untrusted_xml(XmlData) of
        {ok, Xml} -> Xml;
        {error, _} = Error -> Error
    end.

%% @doc Encode a SAMLRequest (or SAMLResponse) as an HTTP-Redirect binding
%%
%% Returns the URI that should be the target of redirection.
-spec encode_http_redirect(IDPTarget :: uri(), SignedXml :: xml(), Username :: undefined | string(), RelayState :: binary()) -> uri().
encode_http_redirect(IdpTarget, SignedXml, Username, RelayState) ->
  Type = xml_payload_type(SignedXml),
  Req = lists:flatten(xmerl:export([SignedXml], xmerl_xml)),

  QueryList = [
               {"SAMLEncoding", ?deflate},
               {Type, base64:encode_to_string(zlib:zip(Req))},
               {"RelayState", uri_string:normalize(binary_to_list(RelayState))}
              ],
  QueryParamStr = uri_string:compose_query(QueryList),
  FirstParamDelimiter = case lists:member($?, IdpTarget) of true -> "&"; false -> "?" end,
  Username_Part = redirect_username_part(Username),

  iolist_to_binary([IdpTarget, FirstParamDelimiter, QueryParamStr | Username_Part]).

redirect_username_part(Username) when is_binary(Username), size(Username) > 0 ->
  ["&", uri_string:compose_query([{"username", uri_string:normalize(binary_to_list(Username))}])];
redirect_username_part(_Other) -> [].

%% @doc Encode a SAMLRequest (or SAMLResponse) as an HTTP-POST binding
%%
%% Returns the HTML document to be sent to the browser, containing a
%% form and javascript to automatically submit it.
-spec encode_http_post(IDPTarget :: uri(), SignedXml :: xml(), RelayState :: binary()) -> html_doc().
encode_http_post(IdpTarget, SignedXml, RelayState) ->
    encode_http_post(IdpTarget, SignedXml, RelayState, <<>>).

-spec encode_http_post(IDPTarget :: uri(), SignedXml :: xml(), RelayState :: binary(), Nonce :: binary()) -> html_doc().
encode_http_post(IdpTarget, SignedXml, RelayState, Nonce) when is_binary(Nonce) ->
    Type = xml_payload_type(SignedXml),
	Req = lists:flatten(xmerl:export([SignedXml], xmerl_xml)),
    generate_post_html(Type, IdpTarget, base64:encode(Req), RelayState, Nonce).

generate_post_html(Type, Dest, Req, RelayState, Nonce) ->
    NonceFragment = case Nonce of
        <<>> -> <<>>;
        _ -> [<<"nonce=\"">>, Nonce, <<"\"">>]
    end,
    iolist_to_binary([<<"<!DOCTYPE html PUBLIC \"-//W3C//DTD XHTML 1.0 Transitional//EN\" \"http://www.w3.org/TR/xhtml1/DTD/xhtml1-transitional.dtd\">
<html xmlns=\"http://www.w3.org/1999/xhtml\" xml:lang=\"en\" lang=\"en\">
<head>
<meta http-equiv=\"content-type\" content=\"text/html; charset=utf-8\" />
<title>POST data</title>
</head>
<body>
<script ">>,NonceFragment,<<">
document.addEventListener('DOMContentLoaded', function () {
document.getElementById('saml-req-form').submit();
});
</script>
<noscript>
<p><strong>Note:</strong> Since your browser does not support JavaScript, you must press the button below once to proceed.</p>
</noscript>
<form id=\"saml-req-form\" method=\"post\" action=\"">>,Dest,<<"\">
<input type=\"hidden\" name=\"">>,Type,<<"\" value=\"">>,Req,<<"\" />
<input type=\"hidden\" name=\"RelayState\" value=\"">>,RelayState,<<"\" />
<noscript><input type=\"submit\" value=\"Submit\" /></noscript>
</form>
</body>
</html>">>]).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

response_xml() ->
    <<"<samlp:Response xmlns:samlp=\"urn:oasis:names:tc:SAML:2.0:protocol\" "
      "xmlns:saml=\"urn:oasis:names:tc:SAML:2.0:assertion\" Version=\"2.0\" "
      "IssueInstant=\"2013-01-01T01:01:01Z\"><samlp:Status><samlp:StatusCode "
      "Value=\"urn:oasis:names:tc:SAML:2.0:status:Success\"/></samlp:Status>"
      "</samlp:Response>">>.

doctype_xml() ->
    <<"<!DOCTYPE samlp:Response SYSTEM \"/nonexistent/esaml-test.dtd\">",
      (response_xml())/binary>>.

oversize_xml(Size) ->
    Open = <<"<samlp:Response xmlns:samlp=\"urn:oasis:names:tc:SAML:2.0:protocol\">">>,
    Close = <<"</samlp:Response>">>,
    <<Open/binary, (binary:copy(<<"a">>, Size))/binary, Close/binary>>.

decode_response_accepts_valid_test() ->
    Xml = response_xml(),
    ?assertMatch(#xmlElement{name = 'samlp:Response'},
                 decode_response(undefined, base64:encode(Xml))),
    ?assertMatch(#xmlElement{name = 'samlp:Response'},
                 decode_response(undefined, base64:encode(zlib:zip(Xml)))),
    ?assertMatch(#xmlElement{name = 'samlp:Response'},
                 decode_response(?deflate, base64:encode(zlib:zip(Xml)))).

decode_response_refuses_doctype_test() ->
    Xml = doctype_xml(),
    ?assertEqual({error, doctype_not_allowed},
                 decode_response(undefined, base64:encode(Xml))),
    ?assertEqual({error, doctype_not_allowed},
                 decode_response(?deflate, base64:encode(zlib:zip(Xml)))).

decode_response_refuses_external_entity_test() ->
    Xml = <<"<!DOCTYPE samlp:Response [<!ENTITY xxe SYSTEM \"file:///etc/passwd\">]>"
            "<samlp:Response xmlns:samlp=\"urn:oasis:names:tc:SAML:2.0:protocol\" "
            "Version=\"2.0\">&xxe;</samlp:Response>">>,
    ?assertEqual({error, doctype_not_allowed},
                 decode_response(undefined, base64:encode(Xml))),
    ?assertEqual({error, doctype_not_allowed},
                 decode_response(?deflate, base64:encode(zlib:zip(Xml)))).

decode_response_refuses_oversize_test() ->
    Xml = oversize_xml(600 * 1024),
    ?assertEqual({error, payload_too_large},
                 decode_response(undefined, base64:encode(Xml))),
    %% DEFLATE data over 512 KB that inflates to a small valid response.
    %% Each 5-byte prefix is an empty, non-final stored block.
    Padded = <<(binary:copy(<<0, 0, 0, 16#FF, 16#FF>>, 110000))/binary,
               (zlib:zip(response_xml()))/binary>>,
    ?assert(byte_size(Padded) > 524288),
    ?assertMatch(#xmlElement{name = 'samlp:Response'},
                 scan_payload(zlib:unzip(Padded))),
    ?assertEqual({error, payload_too_large},
                 decode_response(?deflate, base64:encode(Padded))),
    ?assertEqual({error, payload_too_large},
                 decode_response(undefined, base64:encode(Padded))).

decode_response_refuses_inflated_oversize_test() ->
    Zipped = zlib:zip(oversize_xml(2 * 1024 * 1024)),
    ?assert(byte_size(Zipped) < 524288),
    ?assertEqual({error, payload_too_large},
                 decode_response(?deflate, base64:encode(Zipped))),
    ?assertEqual({error, payload_too_large},
                 decode_response(undefined, base64:encode(Zipped))),
    %% Bad DEFLATE data follows 2 MB of valid output. A full inflation
    %% raises data_error. The bounded inflation stops at 512 KB first.
    Z = zlib:open(),
    ok = zlib:deflateInit(Z, default, deflated, -15, 8, default),
    Head = iolist_to_binary(zlib:deflate(Z, oversize_xml(2 * 1024 * 1024), sync)),
    zlib:close(Z),
    Broken = <<Head/binary, 16#FF, 16#FF>>,
    ?assertError(data_error, zlib:unzip(Broken)),
    ?assertEqual({error, payload_too_large},
                 decode_response(?deflate, base64:encode(Broken))),
    ?assertEqual({error, payload_too_large},
                 decode_response(undefined, base64:encode(Broken))).

decode_response_refuses_utf16_test() ->
    Utf16 = unicode:characters_to_binary(doctype_xml(), utf8, {utf16, big}),
    ?assertEqual({error, encoding_not_allowed},
                 decode_response(undefined, base64:encode(<<16#FE, 16#FF, Utf16/binary>>))),
    ?assertEqual({error, encoding_not_allowed},
                 decode_response(undefined, base64:encode(Utf16))).

decode_response_bad_deflate_raises_test() ->
    ?assertError(data_error, decode_response(?deflate, base64:encode(response_xml()))).

-endif.
