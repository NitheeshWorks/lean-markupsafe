import LeanMarkupsafe
open LeanMarkupsafe

/-!
# HTML Representations

Port of markupsafe `docs/html.rst`, block by block. Python's `__html__`
method is a `HasHtml` instance. Upstream's last output reads
`Markup('<a href="/users/3">&lt;script&gt;</a>')`, but its own `User` class
links to `/user/3`, which is what MarkupSafe 3.0.4 prints and what this port
prints.
-/

namespace Examples.Html

/-! ```python
class Image:
    def __init__(self, url):
        self.url = url

    def __html__(self):
        return f'<img src="{self.url}">'
``` -/
structure Image where
  url : String

instance : HasHtml Image where
  html self := Markup.mk s!"<img src=\"{self.url}\">"

/-! ```pycon
>>> img = Image("/static/logo.png")
>>> Markup(img)
Markup('<img src="/static/logo.png">')
``` -/
def img := Image.mk "/static/logo.png"
def imgMarkup := Markup.of img
#eval imgMarkup   -- Markup.mk "<img src=\"/static/logo.png\">"

/-! ```python
class User:
    def __init__(self, id, name):
        self.id = id
        self.name = name

    def __html__(self):
        return f'<a href="/user/{self.id}">{escape(self.name)}</a>'
``` -/
structure User where
  id : Nat
  name : String

instance : HasHtml User where
  html self := Markup.mk s!"<a href=\"/user/{self.id}\">{escape self.name}</a>"

/-! ```pycon
>>> user = User(3, "<script>")
>>> escape(user)
Markup('<a href="/users/3">&lt;script&gt;</a>')
``` -/
def user := User.mk 3 "<script>"
def userMarkup := Markup.escape user
#eval userMarkup   -- Markup.mk "<a href=\"/user/3\">&lt;script&gt;</a>"

end Examples.Html
