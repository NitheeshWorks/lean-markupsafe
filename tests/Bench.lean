import LeanMarkupsafe

/-!
# Big-input bench: time and memory bounds

Every operation that walks its input must run in linear time, in memory a
small multiple of the input, and with constant stack. Each case below runs one
operation on an input of about 20 MB (or a million items), checks the result,
and fails if it took longer than its time bound or if the process's peak
resident memory during the case exceeded its memory bound (Linux `VmHWM`,
reset before each case).

Before the in-place implementations (`escapeFast`, `unescapeFast`,
`removeTagsFast`, `collapseFast`, `fmtGo`, `percGo`, all proved equal to the
specifications and run through `@[csimp]`), these functions recursed once per
character on a `List Char`: a 24 MB string overflowed the stack.

Run with `lake exe bench [bytes]` (default 20000000), always through
`stack-tools/capped`; `scripts/check.sh` and CI run it.
-/

open LeanMarkupsafe

/-- `k` copies of `s`, built in place (no intermediate list, so building the
input does not raise the process's resident memory). -/
def rep (k : Nat) (s : String) : String := Id.run do
  let mut acc := ""
  for _ in [0:k] do
    acc := acc ++ s
  return acc

/-- About `n` bytes of `unit`, repeated. -/
def fill (n : Nat) (unit : String) : String := rep (n / unit.utf8ByteSize) unit

def textUnit : String := "Tom & Jerry <say> \"hi\", it's lorem ipsum dolor sit amet\n"
def escapedUnit : String := "Tom &amp; Jerry &lt;say&gt; &#34;hi&#34;, it&#39;s &copy; &#x41;&#66;\n"
def tagUnit : String := "<p class=\"x\">hello &amp; <b>world</b></p>  <!-- a note -->\n"

/-- One bench case: build the input (not timed), run, check the result. -/
structure Bench where
  name : String
  input : Nat → String
  run : String → Except String String
  ok : String → String → Bool
  boundMs : Nat := 2000
  boundMB : Nat := 300

def ofExcept : Except FormatError Markup → Except String String
  | .ok m => .ok m.str
  | .error e => .error (toString e)

def benches : List Bench := [
  { name := "escape", input := (fill · textUnit), run := fun s => .ok (escape s).str,
    ok := fun s r => r.length == s.length + (s.length / textUnit.length) * 22 },
  { name := "unescape", input := (fill · escapedUnit), run := fun s => .ok (unescape s),
    ok := fun s r => r.length == (s.length / escapedUnit.length) * 34 },
  { name := "striptags (tags and comments)", input := (fill · tagUnit),
    run := fun s => .ok (Markup.mk s).striptags,
    ok := fun s r => r.length == (s.length / tagUnit.length) * 14 - 1 },
  { name := "Markup.format, a 20 MB argument", input := (fill · textUnit),
    run := fun s => ofExcept ((Markup.mk "<p>{}</p>").format s),
    ok := fun s r => r.length == (escape s).str.length + 7 },
  { name := "Markup.formatWith, a 20 MB template", input := (fill · "lorem {0} ipsum {k}\n"),
    run := fun s => ofExcept ((Markup.mk s).formatWith ["<a>"] [("k", "&")]),
    ok := fun s r => r.length == s.length + (s.length / 20) * 8 },
  { name := "% (Markup.mod), a 20 MB argument", input := (fill · textUnit),
    run := fun s => ofExcept (Markup.mk "<p>%s</p>" % s),
    ok := fun s r => r.length == (escape s).str.length + 7 },
  { name := "% (Markup.mod), a 20 MB template", input := (fill · "lorem %s ipsum %%\n"),
    run := fun s => ofExcept (Markup.mk s % ((List.replicate (s.length / 18) "<"))),
    ok := fun s r => r.length == s.length + (s.length / 18) * 1 },
  { name := "Markup.formatWith, a million {} fields and a million arguments",
    input := fun _ => rep 1000000 "{}",
    run := fun s => ofExcept ((Markup.mk s).formatWith (List.replicate 1000000 "<")),
    ok := fun _ r => r.length == 4000000 },
  { name := "Markup.formatWith, a million {0} fields", input := fun _ => rep 1000000 "{0}",
    run := fun s => ofExcept ((Markup.mk s).formatWith ["<"]),
    ok := fun _ r => r.length == 4000000 },
  { name := "%d of a 20 MB digit string (over the int() limit)", input := (rep · "7"),
    run := fun s => match Markup.mk "%d" % s with
      | .ok m => .error s!"accepted: {m.str.length} chars"
      | .error e => .ok (toString e),
    ok := fun s r => r == toString (intLimitError s.length) },
  { name := "join, a million items", input := fun _ => "",
    run := fun _ => .ok (Markup.join (Markup.mk ", ") ((List.range 1000000).map fun i =>
      if i % 2 == 0 then "<a>" else "b")).str,
    ok := fun _ r => r.length == 1000000 * 2 - 2 + 500000 * 9 + 500000 },
  { name := "times, a million copies", input := fun _ => "",
    run := fun _ => .ok (Markup.times (Markup.mk "<br>") 1000000).str,
    ok := fun _ r => r.length == 4000000 },
  { name := "unescape, a reference of 10 MB of digits", input := fun n => "&#" ++ rep (n / 2) "9" ++ ";",
    run := fun s => .ok (unescape s), ok := fun _ r => r == "\uFFFD" },
  -- Last: a word costs about 80 bytes as a list of markups (24 MB, eight
  -- million words, peaks near 660 MB),
  -- and the allocator keeps that memory for any case after this one.
  { name := "split, 5 MB (a million words)", input := fun n => fill (n / 4) textUnit,
    run := fun s => .ok (toString (Markup.mk s).split.length),
    ok := fun s r => r == toString ((s.length / textUnit.length) * 11) } ]

/-- Reset the peak resident memory (Linux; does nothing elsewhere). -/
def resetPeak : IO Unit :=
  try IO.FS.writeFile "/proc/self/clear_refs" "5" catch _ => pure ()

/-- Peak resident memory in MB since the last reset (Linux `VmHWM`). -/
def peakMB : IO (Option Nat) := do
  try
    let st ← IO.FS.readFile "/proc/self/status"
    let ln := (st.splitOn "\n").find? (·.startsWith "VmHWM:")
    pure <| ln.bind fun l => ((l.drop 6).trimAscii.copy.takeWhile Char.isDigit).copy.toNat?.map (· / 1024)
  catch _ => pure none

/-- `lake exe bench probe <unit> <bytes>`: time `unescape` on about that many
bytes of `unit` repeated, for profiling. -/
def probe (unit : String) (n : Nat) : IO UInt32 := do
  let s := fill n unit
  IO.println s!"input {s.utf8ByteSize} bytes"
  let t0 ← IO.monoMsNow
  let r := unescape s
  IO.println s!"unescape: {r.length} chars in {(← IO.monoMsNow) - t0} ms"
  return 0

def main (args : List String) : IO UInt32 := do
  if let "probe" :: unit :: n :: _ := args then
    return ← probe unit (n.toNat?.getD 1000000)
  let n := (args.head? >>= String.toNat?).getD 20000000
  let mut failures := 0
  for b in benches do
    let inp := b.input n
    -- Touch the input so it is built before the clock starts.
    IO.println s!"..    {b.name}: input {inp.utf8ByteSize} bytes"
    resetPeak
    let t0 ← IO.monoMsNow
    let r := b.run inp
    let good := match r with | .ok out => b.ok inp out | .error _ => false
    let t1 ← IO.monoMsNow
    let ms := t1 - t0
    let mb ← peakMB
    let memOK := (mb.map (decide <| · ≤ b.boundMB)).getD true
    let what := match r with | .ok out => s!"{out.length} chars" | .error e => toString (e.take 60)
    let line := s!"{b.name}: {ms} ms (bound {b.boundMs}), {(mb.map toString).getD "?"} MB (bound {b.boundMB}), {what}"
    if good && ms ≤ b.boundMs && memOK then
      IO.println s!"ok    {line}"
    else
      failures := failures + 1
      IO.println s!"FAIL  {line}"
    (← IO.getStdout).flush
  IO.println s!"{benches.length} benches, {failures} failing"
  return if failures == 0 then 0 else 1
