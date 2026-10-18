import LeanMarkupsafe
open LeanMarkupsafe

/-!
# Working With Safe Text

Port of markupsafe `docs/escaping.rst`. The page is autodoc: its examples
are the docstrings it renders, of `escape`, `Markup` (with `Markup.escape`,
`unescape`, `striptags`), `escape_silent` and `soft_str`, in that order
(`src/markupsafe/__init__.py`). Upstream's `Markup.escape` docstring shows
`Markup('Hello &lt;em&gt;World&lt;/em&gt;!')`; MarkupSafe 3.0.4 keeps the
comma, `Markup('Hello, &lt;em&gt;World&lt;/em&gt;!')`, as here.
-/

namespace Examples.Escaping

/-! `Markup` docstring:
```pycon
>>> Markup("Hello, <em>World</em>!")
Markup('Hello, <em>World</em>!')
>>> Markup(42)
Markup('42')
>>> Markup.escape("Hello, <em>World</em>!")
Markup('Hello &lt;em&gt;World&lt;/em&gt;!')
``` -/
def hello := Markup.of "Hello, <em>World</em>!"
#eval hello          -- Markup.mk "Hello, <em>World</em>!"
def fortyTwo := Markup.of 42
#eval fortyTwo       -- Markup.mk "42"
def helloEscaped := Markup.escape "Hello, <em>World</em>!"
#eval helloEscaped   -- Markup.mk "Hello, &lt;em&gt;World&lt;/em&gt;!"

/-! ```pycon
>>> class Foo:
...     def __html__(self):
...         return '<a href="/foo">foo</a>'
...
>>> Markup(Foo())
Markup('<a href="/foo">foo</a>')
``` -/
structure Foo where

instance : HasHtml Foo where
  html _ := Markup.mk "<a href=\"/foo\">foo</a>"

def foo := Markup.of Foo.mk
#eval foo   -- Markup.mk "<a href=\"/foo\">foo</a>"

/-! ```pycon
>>> Markup("<em>%s</em>") % ("foo & bar",)
Markup('<em>foo &amp; bar</em>')
>>> Markup("<em>Hello</em> ") + "<foo>"
Markup('<em>Hello</em> &lt;foo&gt;')
``` -/
def interpolated := Markup.mk "<em>%s</em>" % ["foo & bar"]
#eval interpolated   -- Except.ok (Markup.mk "<em>foo &amp; bar</em>")
def added := Markup.mk "<em>Hello</em> " ++ "<foo>"
#eval added          -- Markup.mk "<em>Hello</em> &lt;foo&gt;"

/-! `Markup.unescape` docstring:
```pycon
>>> Markup("Main &raquo; <em>About</em>").unescape()
'Main » <em>About</em>'
``` -/
def unescaped := (Markup.mk "Main &raquo; <em>About</em>").unescape
#eval unescaped   -- "Main » <em>About</em>"

/-! `Markup.striptags` docstring:
```pycon
>>> Markup("Main &raquo;\t<em>About</em>").striptags()
'Main » About'
``` -/
def stripped := (Markup.mk "Main &raquo;\t<em>About</em>").striptags
#eval stripped   -- "Main » About"

/-! `escape_silent` docstring:
```pycon
>>> escape(None)
Markup('None')
>>> escape_silent(None)
Markup('')
``` -/
def escapeNone := Markup.escape none
#eval escapeNone    -- Markup.mk "None"
def silentNone := escapeSilent none
#eval silentNone    -- Markup.mk ""

/-! `soft_str` docstring:
```pycon
>>> value = escape("<User 1>")
>>> value
Markup('&lt;User 1&gt;')
>>> escape(str(value))
Markup('&amp;lt;User 1&amp;gt;')
>>> escape(soft_str(value))
Markup('&lt;User 1&gt;')
``` -/
def value := escape "<User 1>"
#eval value                              -- Markup.mk "&lt;User 1&gt;"
def valueAsString := escape (toString value)
#eval valueAsString                      -- Markup.mk "&amp;lt;User 1&amp;gt;"
def valueSoft := Markup.escape (softStr value)
#eval valueSoft                          -- Markup.mk "&lt;User 1&gt;"

end Examples.Escaping
