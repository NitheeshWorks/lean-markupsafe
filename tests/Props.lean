import LeanMarkupsafe

open LeanMarkupsafe

/-!
# Property tests: fast feedback where there is no proof

Generates values with a seeded generator and checks the properties that are
tested rather than proved. Not a substitute for the theorems; the check that
runs in under a second so a mistake surfaces while the change is still in
your head.

Run with `lake exe props`, or a different seed with `lake exe props 12345`.
A failure prints the seed and the value, so it reproduces exactly.
-/

/-- xorshift64*: four lines, no dependency, deterministic from the seed. -/
structure Rng where
  s : UInt64
  deriving Inhabited

def Rng.next (r : Rng) : UInt64 × Rng :=
  let x := r.s
  let x := x ^^^ (x >>> 12)
  let x := x ^^^ (x <<< 25)
  let x := x ^^^ (x >>> 27)
  (x * 2685821657736338717, { s := x })

def Rng.nat (r : Rng) (bound : Nat) : Nat × Rng :=
  let (v, r) := r.next
  (if bound == 0 then 0 else v.toNat % bound, r)

/-- A property: a name and a check that, given a generator, either passes or
returns a description of the failing value. -/
structure Property where
  name : String
  check : Rng → Option String × Rng

/-- Characters that exercise the interesting cases: the five specials,
reference syntax, whitespace, tags, format syntax, and non-ASCII. -/
def alphabet : Array Char :=
  #['a', 'b', 'Z', '0', '3', '9', 'x', '&', '<', '>', '"', '\'', ';', '#', '!', '-', ' ', '\t',
    '\n', ' ', '　', '{', '}', '%', '(', ')', 's', 'é', 'こ', '🍣', 'm', 'p', 'l', 't', 'g']

def Rng.char (r : Rng) : Char × Rng :=
  let (i, r) := r.nat alphabet.size
  (alphabet[i]!, r)

def Rng.string (r : Rng) (maxLen : Nat := 24) : String × Rng := Id.run do
  let (n, r0) := r.nat (maxLen + 1)
  let mut r := r0
  let mut out : List Char := []
  for _ in [0:n] do
    let (c, r') := r.char
    r := r'
    out := c :: out
  return (String.ofList out, r)

/-- Upstream's `_native._escape_inner`: five chained `str.replace` calls,
`&` first. A differential oracle for `escape`. -/
def chainedReplace (s : String) : String :=
  ((((s.replace "&" "&amp;").replace ">" "&gt;").replace "<" "&lt;").replace "'" "&#39;").replace
    "\"" "&#34;"

def prop (name : String) (f : String → Bool) : Property :=
  ⟨name, fun r => let (s, r) := r.string; (if f s then none else some s!"{repr s}", r)⟩

/-- No leading, trailing or doubled space; no other whitespace. -/
def normalised (s : String) : Bool :=
  let l := s.toList
  l.head? != some ' ' && l.getLast? != some ' ' &&
    !(l.zip l.tail).any (fun (a, b) => a == ' ' && b == ' ') &&
    l.all (fun c => c == ' ' || !isPySpace c)

def properties : List Property :=
  [ prop "escape agrees with upstream's chained str.replace" fun s =>
      (escape s).str == chainedReplace s,
    prop "IsEscaped decides true on escape output" fun s => decide (IsEscaped (escape s).str),
    prop "unescape (escape s) = s (smoke test of unescape_escape)" fun s =>
      unescape (escape s).str == s,
    prop "IsEscaped s implies escape (unescape s) = s" fun s =>
      !decide (IsEscaped s) || (escape (unescape s)).str == s,
    prop "unescape is the identity on text without &" fun s =>
      s.toList.contains '&' || unescape s == s,
    prop "unescape never lengthens text" fun s => (unescape s).length ≤ s.length,
    prop "collapseSpaces output is normalised" fun s =>
      normalised (String.ofList (collapseSpaces s.toList)),
    prop "collapseSpaces keeps the non-space characters in order" fun s =>
      (collapseSpaces s.toList).filter (· != ' ') == s.toList.filter (fun c => !isPySpace c),
    prop "removeTags output is a subsequence of the input" fun s =>
      (removeTags s.toList).isSublist s.toList,
    prop "striptags of escaped text is the normalised text" fun s =>
      (escape s).striptags == String.ofList (collapseSpaces s.toList),
    prop "format \"{}\" of a string is its escape" fun s =>
      match (Markup.mk "{}").format [FormatArg.ofString s] with
      | .ok m => m == escape s
      | .error _ => false,
    prop "% with a mapping: the last binding of a repeated key wins, as a Python dict" fun s =>
      match (Markup.mk "%(k)s|%(j)s").mod
          (.mapping [("k", .ofString "x"), ("j", .ofString s), ("k", .ofString s)]) with
      | .ok m => m.str == (escape s).str ++ "|" ++ (escape s).str
      | .error _ => false,
    prop "format keywords: the first binding of a repeated key wins" fun s =>
      match (Markup.mk "{k}").formatWith [] [("k", .ofString s), ("k", .ofString "x")] with
      | .ok m => m == escape s
      | .error _ => false,
    prop "% of an escaped template with a string argument is escaped" fun s =>
      match (escape s ++ Markup.mk " %s").mod (.tuple [.ofString s]) with
      | .ok m => decide (IsEscaped m.str)
      | .error _ => true,
    prop "decimal and hex numeric references agree" fun s =>
      let n := s.length * 977 + 32
      unescape s!"&#{n};" == unescape s!"&#x{String.ofList (Nat.toDigits 16 n)};",
    prop "join of strings is escaped" fun s =>
      decide (IsEscaped (Markup.join (escape s) [s, s]).str) ]

def main (args : List String) : IO UInt32 := do
  let seed := (args.head? >>= String.toNat?).getD 88172645463325252
  let cases := 200
  let mut rng : Rng := { s := UInt64.ofNat seed }
  let mut failures := 0
  for p in properties do
    let mut failed : Option String := none
    for _ in [0:cases] do
      if failed.isSome then break
      let (res, rng') := p.check rng
      rng := rng'
      failed := res
    match failed with
    | none => IO.println s!"ok    {p.name} ({cases} cases)"
    | some why =>
      failures := failures + 1
      IO.println s!"FAIL  {p.name}: {why}  (seed {seed})"
  IO.println s!"{properties.length} properties, {failures} failing (seed {seed})"
  return if failures == 0 then 0 else 1
