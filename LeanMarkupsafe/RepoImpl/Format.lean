import LeanMarkupsafe.RepoImpl.Escape
import LeanMarkupsafe.RepoImpl.Unescape

/-!
# Interpolation: `Markup.format` and `Markup.mod`

Upstream `Markup.format` runs `str.format` with a formatter that escapes every
field, and `Markup.__mod__` runs `%` with every argument wrapped so that
`%s` escapes it. Here a `FormatArg` carries its own (already safe) rendering
under each `Conversion`, and the two template engines copy literal text and
insert the renderings.

Supported `str.format` syntax: literal text, `{{` and `}}`, and fields
`{}`, `{0}`, `{name}`, each with an optional `:spec` handed to the argument.
Supported `%` syntax: `%%`, `%s`, `%d`, `%i`, and `%(key)s`/`%(key)d`/
`%(key)i`. Attribute and index access in fields (`{0.x}`, `{0[1]}`),
`!r`-style conversions, nested specs and `%` flags, widths and precisions
are rejected with `FormatError.unsupported` (deviations recorded in
`docs/traceability.toml`).
-/

namespace LeanMarkupsafe

namespace FormatArg

/-- A string argument: escaped under `%s` and `{}`; `%d` is a type error. -/
def ofString (s : String) : FormatArg where
  render
    | .percentStr => .ok (escape s)
    | .percentInt => .error (.typeError "%d format: a real number is required, not str")
    | .brace spec =>
      if spec.isEmpty then .ok (escape s)
      else .error (.unsupported s!"format spec '{spec}' for a string")

/-- An integer argument: its decimal text under every conversion. -/
def ofInt (i : Int) : FormatArg where
  render
    | .percentStr => .ok (escape (toString i))
    | .percentInt => .ok (escape (toString i))
    | .brace spec =>
      if spec.isEmpty then .ok (escape (toString i))
      else .error (.unsupported s!"format spec '{spec}' for an integer")

/-- A natural-number argument, as `ofInt`. -/
def ofNat (n : Nat) : FormatArg := ofInt n

/-- A `HasHtml` argument: its HTML rendering, unescaped; a format spec is an
error, as upstream raises when a class defines `__html__` but not
`__html_format__`. -/
def ofHtml {α : Type u} [HasHtml α] (x : α) : FormatArg where
  render
    | .percentStr => .ok (HasHtml.html x)
    | .percentInt => .error (.typeError "%d format: a real number is required")
    | .brace spec =>
      if spec.isEmpty then .ok (HasHtml.html x)
      else .error (.unsupportedSpec s!"Format specifier {spec} given, but the value does not define __html_format__. A class that defines __html__ must define __html_format__ to work with format specifiers.")

/-- A `Markup` argument: inserted verbatim; a format spec is an error
(upstream `Markup.__html_format__`). -/
def ofMarkup (m : Markup) : FormatArg where
  render
    | .percentStr => .ok m
    | .percentInt => .error (.typeError "%d format: a real number is required, not Markup")
    | .brace spec =>
      if spec.isEmpty then .ok m
      else .error (.unsupportedSpec "Unsupported format specification for Markup.")

/-- A `HasHtmlFormat` argument: every brace field goes through
`htmlFormat` with its spec (upstream `__html_format__`). -/
def ofHtmlFormat {α : Type u} [HasHtmlFormat α] (x : α) : FormatArg where
  render
    | .percentStr => .ok (HasHtml.html x)
    | .percentInt => .error (.typeError "%d format: a real number is required")
    | .brace spec => HasHtmlFormat.htmlFormat x spec

end FormatArg

/-- Values that can be passed to `format`/`%`. -/
class ToFormatArg (α : Type u) where
  toFormatArg : α → FormatArg

instance : ToFormatArg FormatArg := ⟨id⟩
instance : ToFormatArg String := ⟨FormatArg.ofString⟩
instance : ToFormatArg Markup := ⟨FormatArg.ofMarkup⟩
instance : ToFormatArg Int := ⟨FormatArg.ofInt⟩
instance : ToFormatArg Nat := ⟨FormatArg.ofNat⟩
instance (priority := 200) {α : Type u} [HasHtmlFormat α] : ToFormatArg α :=
  ⟨FormatArg.ofHtmlFormat⟩
instance (priority := low) {α : Type u} [HasHtml α] : ToFormatArg α := ⟨FormatArg.ofHtml⟩

/-- Map the success value, keep the error. -/
def mapOk (f : List Char → List Char) : Except FormatError (List Char) → Except FormatError (List Char)
  | .ok o => .ok (f o)
  | .error e => .error e

/-! ## `str.format` -/

/-- Field numbering state: no field yet, automatic (`{}`, next index), or
manual (`{0}`). Upstream rejects mixing the two. -/
inductive Numbering where
  | unset
  | auto (next : Nat)
  | manual
  deriving DecidableEq, Repr

/-- The contents of a field up to its closing `}`, and the rest after it. -/
def takeField : List Char → Except FormatError (List Char × List Char)
  | [] => .error (.badTemplate "expected '}' before end of string")
  | c :: l =>
    if c = '}' then .ok ([], l)
    else if c = '{' then .error (.unsupported "nested replacement fields in a format spec")
    else match takeField l with
      | .ok (f, r) => .ok (c :: f, r)
      | .error e => .error e

theorem takeField_spec {l f r : List Char} (h : takeField l = .ok (f, r)) :
    l = f ++ '}' :: r := by
  induction l generalizing f with
  | nil => simp [takeField] at h
  | cons c l ih =>
    unfold takeField at h
    split at h
    · cases h; simp_all
    · split at h
      · cases h
      · split at h
        · rename_i f' r' heq
          cases h; rw [ih heq]; rfl
        · cases h

theorem takeField_length {l f r : List Char} (h : takeField l = .ok (f, r)) :
    r.length < l.length := by
  rw [takeField_spec h]; simp; omega

/-- Split a field into its name and its spec (after the first `:`). -/
def splitField (field : List Char) : List Char × List Char :=
  let name := field.takeWhile (· ≠ ':')
  (name, (field.drop name.length).drop 1)

/-- Look up the argument a field names, advancing the numbering. -/
def resolveField (pos : List FormatArg) (named : List (String × FormatArg))
    (st : Numbering) (name : List Char) : Except FormatError (FormatArg × Numbering) :=
  if name.any (fun c => c = '.' || c = '[' || c = '!') then
    .error (.unsupported "attribute, index or conversion in a format field")
  else if name.isEmpty then
    match st with
    | .manual => .error .mixedNumbering
    | .unset | .auto _ =>
      let i := match st with | .auto n => n | _ => 0
      match pos[i]? with
      | some a => .ok (a, .auto (i + 1))
      | none => .error (.indexOutOfRange i)
  else if name.all isDecDigit then
    match st with
    | .auto _ => .error .mixedNumbering
    | .unset | .manual =>
      let i := decValue name
      match pos[i]? with
      | some a => .ok (a, .manual)
      | none => .error (.indexOutOfRange i)
  else
    let key := String.ofList name
    match named.lookup key with
    | some a => .ok (a, st)
    | none => .error (.missingKey key)

/-- Render one field. -/
def renderField (pos : List FormatArg) (named : List (String × FormatArg))
    (st : Numbering) (field : List Char) : Except FormatError (Markup × Numbering) :=
  let nf := splitField field
  match resolveField pos named st nf.1 with
  | .error e => .error e
  | .ok (a, st') =>
    match a.render (.brace (String.ofList nf.2)) with
    | .error e => .error e
    | .ok m => .ok (m, st')

/-- The `str.format` engine on a character list. -/
def formatList (pos : List FormatArg) (named : List (String × FormatArg)) :
    Numbering → List Char → Except FormatError (List Char)
  | _, [] => .ok []
  | st, c :: l =>
    if c = '{' then
      if l.head? = some '{' then mapOk ('{' :: ·) (formatList pos named st l.tail)
      else
        match h : takeField l with
        | .error e => .error e
        | .ok (field, r) =>
          have : r.length < l.length + 1 := by have := takeField_length h; omega
          match renderField pos named st field with
          | .error e => .error e
          | .ok (m, st') => mapOk (m.str.toList ++ ·) (formatList pos named st' r)
    else if c = '}' then
      if l.head? = some '}' then mapOk ('}' :: ·) (formatList pos named st l.tail)
      else .error (.badTemplate "Single '}' encountered in format string")
    else mapOk (c :: ·) (formatList pos named st l)
termination_by _ l => l.length

/-- `str.format` on markup, escaping every argument that is not already safe
(upstream `Markup.format`; `format_map` is the `named`-only case). -/
def Markup.format (t : Markup) (pos : List FormatArg)
    (named : List (String × FormatArg) := []) : Except FormatError Markup :=
  match formatList pos named .unset t.str.toList with
  | .ok o => .ok ⟨String.ofList o⟩
  | .error e => .error e

/-- Upstream `Markup.format_map`. -/
def Markup.formatMap (t : Markup) (named : List (String × FormatArg)) :
    Except FormatError Markup :=
  t.format [] named

/-! ## `%` -/

/-- A `%` key up to its `)`, and the rest after it. -/
def takeKey : List Char → Option (List Char × List Char)
  | [] => none
  | c :: l =>
    if c = ')' then some ([], l)
    else match takeKey l with
      | some (k, r) => some (c :: k, r)
      | none => none

theorem takeKey_spec {l k r : List Char} (h : takeKey l = some (k, r)) :
    l = k ++ ')' :: r := by
  induction l generalizing k with
  | nil => simp [takeKey] at h
  | cons c l ih =>
    unfold takeKey at h
    split at h
    · cases h; simp_all
    · split at h
      · rename_i k' r' heq
        cases h; rw [ih heq]; rfl
      · cases h

theorem takeKey_length {l k r : List Char} (h : takeKey l = some (k, r)) :
    r.length < l.length := by
  rw [takeKey_spec h]; simp; omega

/-- The conversion a `%` conversion character asks for, or why not. -/
def percentConv (c : Char) : Except FormatError Conversion :=
  if c = 's' then .ok .percentStr
  else if c = 'd' ∨ c = 'i' then .ok .percentInt
  else if ['r', 'a', 'c', 'x', 'X', 'o', 'e', 'E', 'f', 'F', 'g', 'G', 'u', '-', '+', ' ', '#',
      '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', '.', '*'].contains c then
    .error (.unsupported s!"%-format conversion, flag or width '{c}'")
  else .error (.badTemplate s!"unsupported format character '{c}'")

/-- The `%` engine. `map` is the mapping for `%(key)s` fields, if the
arguments are a mapping; `rem` the positional arguments not yet used. -/
def percentList (map : Option (List (String × FormatArg))) :
    List FormatArg → List Char → Except FormatError (List Char)
  | rem, [] =>
    if map.isNone ∧ ¬ rem.isEmpty then .error .notAllConverted else .ok []
  | rem, c :: l =>
    if c = '%' then
      match hl : l with
      | [] => .error (.badTemplate "incomplete format")
      | d :: r =>
        if d = '%' then mapOk ('%' :: ·) (percentList map rem r)
        else if d = '(' then
          match h : takeKey r with
          | none => .error (.badTemplate "incomplete format key")
          | some (key, r') =>
            match r' with
            | [] => .error (.badTemplate "incomplete format")
            | cv :: r'' =>
              have : r''.length < r.length + 1 + 1 := by
                have := takeKey_length h; simp at this; omega
              match map with
              | none => .error .requiresMapping
              | some kv =>
                match percentConv cv with
                | .error e => .error e
                | .ok conv =>
                  match kv.lookup (String.ofList key) with
                  | none => .error (.missingKey (String.ofList key))
                  | some a =>
                    match a.render conv with
                    | .error e => .error e
                    | .ok m => mapOk (m.str.toList ++ ·) (percentList map rem r'')
        else
          match percentConv d with
          | .error e => .error e
          | .ok conv =>
            match map with
            | some _ => .error (.unsupported "a positional % field with mapping arguments")
            | none =>
              match rem with
              | [] => .error .notEnoughArguments
              | a :: rem' =>
                match a.render conv with
                | .error e => .error e
                | .ok m => mapOk (m.str.toList ++ ·) (percentList map rem' r)
    else mapOk (c :: ·) (percentList map rem l)
termination_by _ l => l.length

/-- `%` interpolation on markup, escaping every argument that is not already
safe (upstream `Markup.__mod__`). -/
def Markup.mod (t : Markup) (args : PercentArgs) : Except FormatError Markup :=
  let r := match args with
    | .tuple xs => percentList none xs t.str.toList
    | .mapping kv => percentList (some kv) [] t.str.toList
  match r with
  | .ok o => .ok ⟨String.ofList o⟩
  | .error e => .error e

/-- `t % args` for a tuple of arguments. -/
instance : HMod Markup (List FormatArg) (Except FormatError Markup) :=
  ⟨fun t xs => t.mod (.tuple xs)⟩

/-- `t % arg` for a single argument (upstream wraps it in a 1-tuple). -/
instance : HMod Markup FormatArg (Except FormatError Markup) :=
  ⟨fun t x => t.mod (.tuple [x])⟩

end LeanMarkupsafe
