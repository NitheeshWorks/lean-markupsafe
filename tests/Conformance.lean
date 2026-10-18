import LeanMarkupsafe

/-!
# Conformance cases

Each case re-expresses one upstream test (https://github.com/pallets/markupsafe, `tests/`) in Lean and
names it, so `docs/traceability.toml` can point at both. The upstream suite is
the behavioural specification; no upstream code is copied.

Run with `lake exe conformance`.
-/

open LeanMarkupsafe

structure Case where
  /-- Upstream test this mirrors, e.g. `tests/test_path.py::test_int`. -/
  upstream : String
  name : String
  run : IO Bool

def check (upstream name : String) (b : Bool) : Case := ⟨upstream, name, pure b⟩

def okStr (r : Except FormatError Markup) (expect : String) : Bool :=
  match r with
  | .ok m => m.str == expect
  | .error _ => false

def isErr (r : Except FormatError Markup) : Bool :=
  match r with
  | .ok _ => false
  | .error _ => true

/-- A value with only `__html__` (upstream `HasHTMLOnly`, `Foo`). -/
structure HtmlOnly where
  html : String

instance : HasHtml HtmlOnly := ⟨fun x => Markup.mk x.html⟩

/-- A value with `__html__` and `__html_format__` (upstream `HasHTMLAndFormat`). -/
structure HtmlAndFormat where
  unit : Unit := ()

instance : HasHtmlFormat HtmlAndFormat where
  html _ := Markup.mk "<foo>"
  htmlFormat _ _ := .ok (Markup.mk "<FORMAT>")

/-- Upstream `test_complex_custom_formatting`'s `User`. -/
structure User where
  id : Nat
  username : String

def User.toHtml (u : User) : Markup :=
  match (Markup.mk "<span class=user>{0}</span>").format [.ofString u.username] with
  | .ok m => m
  | .error _ => Markup.empty

instance : HasHtmlFormat User where
  html := User.toHtml
  htmlFormat u spec :=
    if spec == "link" then
      (Markup.mk "<a href=\"/user/{0}\">{1}</a>").format [.ofNat u.id, .ofMarkup u.toHtml]
    else if spec.isEmpty then .ok u.toHtml
    else .error (.unsupportedSpec "Invalid format spec")

def escapeCases : List (String × String) :=
  [("", ""),
   ("abcd&><'\"efgh", "abcd&amp;&gt;&lt;&#39;&#34;efgh"),
   ("&><'\"efgh", "&amp;&gt;&lt;&#39;&#34;efgh"),
   ("abcd&><'\"", "abcd&amp;&gt;&lt;&#39;&#34;"),
   ("こんにちは&><'\"こんばんは", "こんにちは&amp;&gt;&lt;&#39;&#34;こんばんは"),
   ("&><'\"こんばんは", "&amp;&gt;&lt;&#39;&#34;こんばんは"),
   ("こんにちは&><'\"", "こんにちは&amp;&gt;&lt;&#39;&#34;"),
   ("🍣🍢&><'\"🍺 xyz", "🍣🍢&amp;&gt;&lt;&#39;&#34;🍺 xyz"),
   ("&><'\"🍺 xyz", "&amp;&gt;&lt;&#39;&#34;🍺 xyz"),
   ("🍣🍢&><'\"", "🍣🍢&amp;&gt;&lt;&#39;&#34;")]

def decodeHex (s : String) : String :=
  String.ofList ((s.splitOn " ").filter (· ≠ "") |>.map fun h =>
    Char.ofNat (h.toList.foldl (fun n c => 16 * n + hexDigitValue c) 0))

/-- Every line of `tests/fixtures/unescape.txt` (generated from CPython's
`html.unescape` by `scripts/gen-unescape-fixture.py`) must match. -/
def unescapeFixture : Case where
  upstream := "src/markupsafe/__init__.py::Markup.unescape (html.unescape differential fixture)"
  name := "unescape_fixture"
  run := do
    let text ← IO.FS.readFile "tests/fixtures/unescape.txt"
    let mut bad := 0
    let mut total := 0
    for line in text.splitOn "\n" do
      if line.isEmpty then continue
      match line.splitOn "\t" with
      | [i, o] =>
        total := total + 1
        let inp := decodeHex i
        if unescape inp != decodeHex o then
          if bad < 5 then IO.println s!"      mismatch: {repr inp} -> {repr (unescape inp)}"
          bad := bad + 1
      | _ => bad := bad + 1
    IO.println s!"      {total} fixture lines, {bad} mismatches"
    return bad == 0 && total > 10000

def cases : List Case :=
  (escapeCases.zipIdx.map fun ((v, e), i) =>
    check "tests/test_escape.py::test_escape" s!"escape[{i}]" ((escape v).str == e)) ++
  [ check "tests/test_markupsafe.py::test_adding" "adding"
      (let untrusted := "<script type=\"application/x-some-script\">alert(\"foo\");</script>"
       let safe := Markup.mk "<em>username</em>"
       (untrusted ++ safe).str == (escape untrusted).str ++ safe.str),
    check "tests/test_markupsafe.py::test_string_interpolation" "interpolation[%s]"
      (okStr ((Markup.mk "<em>%s</em>") % FormatArg.ofString "<bad user>") "<em>&lt;bad user&gt;</em>"),
    check "tests/test_markupsafe.py::test_string_interpolation" "interpolation[%(username)s]"
      (okStr ((Markup.mk "<em>%(username)s</em>").mod (.mapping [("username", .ofString "<bad user>")]))
        "<em>&lt;bad user&gt;</em>"),
    check "tests/test_markupsafe.py::test_string_interpolation" "interpolation[%i] (integer argument)"
      (okStr ((Markup.mk "%i") % FormatArg.ofInt 3) "3"),
    check "src/markupsafe/__init__.py::_MarkupEscapeHelper.__int__" "percent_d_of_text"
      (okStr ((Markup.mk "%d") % FormatArg.ofString "5") "5" &&
       okStr ((Markup.mk "%d") % FormatArg.ofString " -12 ") "-12" &&
       okStr ((Markup.mk "%i") % FormatArg.ofString "1_000") "1000" &&
       isErr ((Markup.mk "%d") % FormatArg.ofString "x") &&
       okStr ((Markup.mk "%d") % FormatArg.ofMarkup (Markup.mk "7")) "7"),
    check "tests/test_markupsafe.py::test_escape_silent" "escape_none"
      (Markup.escape (none : Option String) == Markup.mk "None" &&
       Markup.escape (some "<") == Markup.mk "&lt;"),
    check "tests/test_markupsafe.py::test_string_interpolation" "trusted_template_provenance"
      (match API.formatStrings (Markup.mk "<em>{}</em>") ["<bad user>"] with
       | .ok r => r.val.str == "<em>&lt;bad user&gt;</em>"
       | .error _ => false),
    check "src/markupsafe/__init__.py::Markup.__mod__" "positional_with_mapping"
      (isErr ((Markup.mk "%s").mod (.mapping [("a", .ofNat 1)]))),
    check "README.md (Examples)" "readme_examples"
      ((escape "<script>alert(document.cookie);</script>").str ==
         "&lt;script&gt;alert(document.cookie);&lt;/script&gt;" &&
       Markup.escape (Markup.mk "<strong>Hello</strong>") == Markup.mk "<strong>Hello</strong>" &&
       okStr ((Markup.mk "Hello <em>{name}</em>").format [] [("name", "\"World\"")])
         "Hello <em>&#34;World&#34;</em>" &&
       okStr ((Markup.mk "<em>{}</em> {}").format ["<x>", (3 : Nat)]) "<em>&lt;x&gt;</em> 3"),
    check "tests/test_markupsafe.py::test_type_behavior" "type_behavior"
      ((Markup.mk "foo" ++ "bar").str == "foobar" && HasHtml.html (Markup.mk "foo") == Markup.mk "foo"),
    check "tests/test_markupsafe.py::test_html_interop" "html_interop"
      ((Markup.ofHtml (HtmlOnly.mk "<em>awesome</em>")).str == "<em>awesome</em>" &&
       okStr ((Markup.mk "<strong>%s</strong>") % FormatArg.ofHtml (HtmlOnly.mk "<em>awesome</em>"))
         "<strong><em>awesome</em></strong>"),
    check "tests/test_markupsafe.py::test_missing_interpol" "missing_interpol[foo]"
      (isErr ((Markup.mk "<em></em>") % FormatArg.ofString "foo")),
    check "tests/test_markupsafe.py::test_missing_interpol" "missing_interpol[42]"
      (isErr ((Markup.mk "<em></em>") % FormatArg.ofInt 42)),
    check "tests/test_markupsafe.py::test_missing_interpol" "missing_interpol[(foo, 42)]"
      (isErr ((Markup.mk "<em></em>") % [FormatArg.ofString "foo", .ofInt 42])),
    check "tests/test_markupsafe.py::test_tuple_interpol" "tuple_interpol"
      (okStr ((Markup.mk "<em>%s:%s</em>") % [FormatArg.ofString "<foo>", .ofString "<bar>"])
        "<em>&lt;foo&gt;:&lt;bar&gt;</em>"),
    check "tests/test_markupsafe.py::test_dict_interpol" "dict_interpol"
      (okStr ((Markup.mk "<em>%(foo)s</em>").mod (.mapping [("foo", .ofString "<foo>")]))
         "<em>&lt;foo&gt;</em>" &&
       okStr ((Markup.mk "<em>%(foo)s:%(bar)s</em>").mod
         (.mapping [("foo", .ofString "<foo>"), ("bar", .ofString "<bar>")]))
         "<em>&lt;foo&gt;:&lt;bar&gt;</em>"),
    check "tests/test_markupsafe.py::test_escaping" "escaping"
      ((escape "\"<>&'").str == "&#34;&lt;&gt;&amp;&#39;" &&
       (Markup.mk ("<!-- outer comment -->" ++ "<em>Foo &amp; Bar" ++
          " <!-- inner comment about <em> -->\n " ++ "</em>" ++
          "<!-- comment\nwith\nnewlines\n-->" ++
          "<meta content='tag\nwith\nnewlines'>")).striptags == "Foo & Bar"),
    check "tests/test_markupsafe.py::test_unescape" "unescape"
      ((Markup.mk "&lt;test&gt;").unescape == "<test>" &&
       (Markup.mk "jack & tavi are cooler than mike &amp; russ").unescape ==
         "jack & tavi are cooler than mike & russ" &&
       (let once := (Markup.mk "&foo&#x3b;").unescape
        let twice := (Markup.mk once).unescape
        once == "&foo;" && twice == "&foo;")),
    check "tests/test_markupsafe.py::test_format" "format[named]"
      (okStr ((Markup.mk "<em>{awesome}</em>").format [] [("awesome", .ofString "<awesome>")])
        "<em>&lt;awesome&gt;</em>"),
    check "tests/test_markupsafe.py::test_format" "format[index access rejected: deviation]"
      (isErr ((Markup.mk "{0[1][bar]}").format [.ofString "x"])),
    check "tests/test_markupsafe.py::test_format_map" "format_map"
      (okStr ((Markup.mk "<em>{value}</em>").formatMap [("value", .ofString "<value>")])
        "<em>&lt;value&gt;</em>"),
    check "tests/test_markupsafe.py::test_formatting_empty" "formatting_empty"
      (okStr ((Markup.mk "{}").format [.ofNat 0]) "0"),
    check "tests/test_markupsafe.py::test_custom_formatting" "custom_formatting"
      (okStr ((Markup.mk "{0}").format [ToFormatArg.toFormatArg (HtmlOnly.mk "<foo>")]) "<foo>" &&
       okStr ((Markup.mk "{0}").format [ToFormatArg.toFormatArg (HtmlAndFormat.mk ())]) "<FORMAT>"),
    check "tests/test_markupsafe.py::test_complex_custom_formatting" "complex_custom_formatting"
      (okStr ((Markup.mk "<p>User: {0:link}").format [ToFormatArg.toFormatArg (User.mk 1 "foo")])
        "<p>User: <a href=\"/user/1\"><span class=user>foo</span></a>"),
    check "tests/test_markupsafe.py::test_formatting_with_objects" "formatting_with_objects"
      (okStr ((Markup.mk "{s}").format [] [("s", .ofString "строка")]) "строка"),
    check "tests/test_markupsafe.py::test_escape_silent" "escape_silent"
      (escapeSilent (none : Option String) == Markup.empty &&
       escapeSilent (some "<foo>") == Markup.mk "&lt;foo&gt;"),
    check "tests/test_markupsafe.py::test_splitting" "splitting[split]"
      ((Markup.mk "a b").split == [Markup.mk "a", Markup.mk "b"]),
    check "tests/test_markupsafe.py::test_mul" "mul"
      ((Markup.mk "a").times 3 == Markup.mk "aaa"),
    check "tests/test_markupsafe.py::test_escape_return_type" "escape_return_type"
      (Markup.escape "a" == Markup.mk "a" && Markup.escape (Markup.mk "a") == Markup.mk "a" &&
       Markup.escape (HtmlOnly.mk "<strong>Foo</strong>") == Markup.mk "<strong>Foo</strong>"),
    check "tests/test_markupsafe.py::test_soft_str" "soft_str"
      (softStr "" == .plain "" && softStr Markup.empty == .markup Markup.empty &&
       softStr (15 : Nat) == .plain "15"),
    check "src/markupsafe/__init__.py::soft_str (docstring)" "soft_str_docstring"
      (let value := escape "<User 1>"
       value.str == "&lt;User 1&gt;" && (escape value.str).str == "&amp;lt;User 1&amp;gt;" &&
       Markup.escape (softStr value) == value),
    check "src/markupsafe/__init__.py::Markup.striptags (docstring)" "striptags_docstring"
      ((Markup.mk "Main &raquo;\t<em>About</em>").striptags == "Main » About"),
    check "src/markupsafe/__init__.py::Markup.unescape (docstring)" "unescape_docstring"
      ((Markup.mk "Main &raquo; <em>About</em>").unescape == "Main » <em>About</em>"),
    check "src/markupsafe/__init__.py::Markup (docstring)" "markup_docstring"
      ((Markup.mk "<em>Hello</em> " ++ "<foo>").str == "<em>Hello</em> &lt;foo&gt;" &&
       (Markup.escape "Hello, <em>World</em>!").str == "Hello, &lt;em&gt;World&lt;/em&gt;!"),
    check "html.entities.html5 (table used by Markup.unescape)" "entity_table_size"
      (entityMap.size == Entities.count),
    check "html.entities.html5 (table used by Markup.unescape)" "entity_fast_path_agrees"
      (["amp;", "lt;", "gt;"].all fun n =>
        lookupNamed n.toList == (entityMap.get? n).map String.toList),
    check "html.unescape (numeric references)" "numeric_references"
      (unescape "&#0;&#13;&#128;&#x110000;&#xD800;&#1;&#65;&#x41;&#X41;&#65" ==
        "�\r€��AAAA"),
    unescapeFixture,
    check "html.unescape (named prefix fallback)" "named_prefix_fallback"
      (unescape "&notit; &amp &ampx; &zz;" == "¬it; & &x; &zz;") ]

def main : IO UInt32 := do
  let mut failures := 0
  for c in cases do
    let ok ← try c.run catch e => do IO.println s!"      {e}"; pure false
    IO.println s!"{if ok then "ok  " else "FAIL"}  {c.name}  [{c.upstream}]"
    unless ok do failures := failures + 1
  IO.println s!"{cases.length} cases, {failures} failing"
  return if failures == 0 then 0 else 1
