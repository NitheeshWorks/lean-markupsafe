import LeanMarkupsafe
open LeanMarkupsafe

/-!
# MarkupSafe (docs index)

Port of markupsafe `docs/index.rst`, statement by statement. Upstream's
`escape(obj)` on an object that may already be markup is `Markup.escape` here;
`escape` takes a `String`.
-/

namespace Examples.Index

/-! ```pycon
>>> from markupsafe import escape
>>> hello = escape("<em>Hello</em>")
>>> hello
Markup('&lt;em&gt;Hello&lt;/em&gt;')
``` -/
def hello := escape "<em>Hello</em>"
#eval hello   -- Markup.mk "&lt;em&gt;Hello&lt;/em&gt;"

/-! ```pycon
>>> escape(hello)
Markup('&lt;em&gt;Hello&lt;/em&gt;')
``` -/
def escapedAgain := Markup.escape hello
#eval escapedAgain   -- Markup.mk "&lt;em&gt;Hello&lt;/em&gt;"

/-! ```pycon
>>> hello + " <strong>World</strong>"
Markup('&lt;em&gt;Hello&lt;/em&gt; &lt;strong&gt;World&lt;/strong&gt;')
``` -/
def greeting := hello ++ " <strong>World</strong>"
#eval greeting   -- Markup.mk "&lt;em&gt;Hello&lt;/em&gt; &lt;strong&gt;World&lt;/strong&gt;"

end Examples.Index
