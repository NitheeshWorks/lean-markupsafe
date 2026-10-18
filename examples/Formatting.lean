import LeanMarkupsafe
open LeanMarkupsafe

/-!
# String Formatting

Port of markupsafe `docs/formatting.rst`, block by block. Python's
`__html_format__` and `__html__` methods are functions in the `User`
namespace, registered as a `HasHtmlFormat` instance.
`__html__` must return markup, so it uses `format!`, which raises (panics)
on a bad template as Python's `format` would.
-/

namespace Examples.Formatting

/-! ```python
class User(object):
    def __init__(self, id, name):
        self.id = id
        self.name = name

    def __html_format__(self, format_spec):
        if format_spec == "link":
            return Markup(
                '<a href="/user/{}">{}</a>'
            ).format(self.id, self.__html__())
        elif format_spec:
            raise ValueError("Invalid format spec")
        return self.__html__()

    def __html__(self):
        return Markup(
            '<span class="user">{0}</span>'
        ).format(self.name)
``` -/
structure User where
  id : Nat
  name : String

def User.html (self : User) : Markup :=
  (Markup.mk "<span class=\"user\">{0}</span>").format! self.name

def User.htmlFormat (self : User) (formatSpec : String) : Except FormatError Markup :=
  if formatSpec == "link" then
    (Markup.mk "<a href=\"/user/{}\">{}</a>").format (self.id, self.html)
  else if !formatSpec.isEmpty then
    .error (.unsupportedSpec "Invalid format spec")
  else .ok self.html

instance : HasHtmlFormat User where
  html := User.html
  htmlFormat := User.htmlFormat

/-! ```pycon
>>> user = User(3, "<script>")
>>> escape(user)
Markup('<span class="user">&lt;script&gt;</span>')
>>> Markup("<p>User: {user:link}").format(user=user)
Markup('<p>User: <a href="/user/3"><span class="user">&lt;script&gt;</span></a>
``` -/
def user := User.mk 3 "<script>"
def escaped := Markup.escape user
#eval escaped   -- Markup.mk "<span class=\"user\">&lt;script&gt;</span>"
def linked := (Markup.mk "<p>User: {user:link}").format [("user", user)]
#eval linked
-- Except.ok (Markup.mk "<p>User: <a href=\"/user/3\"><span class=\"user\">&lt;script&gt;</span></a>")

/-! printf-style Formatting:
```pycon
>>> user = User(3, "<script>")
>>> Markup('<a href="/user/%d">%s</a>') % (user.id, user.name)
Markup('<a href="/user/3">&lt;script&gt;</a>')
``` -/
def printf := Markup.mk "<a href=\"/user/%d\">%s</a>" % (user.id, user.name)
#eval printf   -- Except.ok (Markup.mk "<a href=\"/user/3\">&lt;script&gt;</a>")

end Examples.Formatting
