import LeanMarkupsafe
open LeanMarkupsafe

/-!
# MarkupSafe: README examples

Port of markupsafe `README.md` ("Examples"), statement by statement. Upstream's
README shows `Markup('<strong>hello</strong>')` for the second and third
results; MarkupSafe 3.0.4 prints `Hello` with a capital H, as here.
-/

namespace Examples.Readme

/-! ```pycon
>>> from markupsafe import Markup, escape
``` -/
-- `import LeanMarkupsafe` and `open LeanMarkupsafe`, above.

/-! ```pycon
>>> # escape replaces special characters and wraps in Markup
>>> escape("<script>alert(document.cookie);</script>")
Markup('&lt;script&gt;alert(document.cookie);&lt;/script&gt;')
``` -/
def escaped := escape "<script>alert(document.cookie);</script>"
#eval escaped   -- Markup.mk "&lt;script&gt;alert(document.cookie);&lt;/script&gt;"

/-! ```pycon
>>> # wrap in Markup to mark text "safe" and prevent escaping
>>> Markup("<strong>Hello</strong>")
Markup('<strong>hello</strong>')
``` -/
def marked := Markup.mk "<strong>Hello</strong>"
#eval marked    -- Markup.mk "<strong>Hello</strong>"

/-! ```pycon
>>> escape(Markup("<strong>Hello</strong>"))
Markup('<strong>hello</strong>')
``` -/
def notEscapedAgain := Markup.escape (Markup.mk "<strong>Hello</strong>")
#eval notEscapedAgain   -- Markup.mk "<strong>Hello</strong>"

/-! ```pycon
>>> # Markup is a str subclass
>>> # methods and operators escape their arguments
>>> template = Markup("Hello <em>{name}</em>")
>>> template.format(name='"World"')
Markup('Hello <em>&#34;World&#34;</em>')
``` -/
def template := Markup.mk "Hello <em>{name}</em>"
def formatted := template.format [("name", "\"World\"")]
#eval formatted   -- Except.ok (Markup.mk "Hello <em>&#34;World&#34;</em>")

end Examples.Readme
