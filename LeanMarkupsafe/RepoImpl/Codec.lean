import Keel.Codec
import LeanMarkupsafe.RepoImpl.Escape

/-!
# Escaping as a Keel codec: the decoder

`escapedChar` reads back one escaped character: a character `escape` keeps,
or one of the five references it emits. Together with `escapeChar` it forms
a lawful `Keel.Codec` (`Proofs/Codec.lean`), and `Keel.Codec.many` lifts it to
whole strings, so the escape round trips are instances of the codec law.
-/

namespace LeanMarkupsafe

open Keel Parser

/-- Read one escaped character. -/
def escapedChar {ε : Type} [ParseError ε] : Parser Char ε Char := do
  let c ← next
  if c = '&' then
    let n ← next
    if n = 'a' then lit ['m', 'p', ';'] *> pure '&'
    else if n = 'l' then lit ['t', ';'] *> pure '<'
    else if n = 'g' then lit ['t', ';'] *> pure '>'
    else if n = '#' then do
      lit ['3']
      let d ← next
      if d = '4' then lit [';'] *> pure '"'
      else if d = '9' then lit [';'] *> pure '\''
      else fail ParseError.unexpected
    else fail ParseError.unexpected
  else if escapeChar c = [c] then pure c
  else fail ParseError.unexpected

end LeanMarkupsafe
