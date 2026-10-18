import LeanMarkupsafe.Proofs.Escape
import LeanMarkupsafe.Proofs.Codec
import LeanMarkupsafe.Proofs.Closure
import LeanMarkupsafe.Proofs.StripTags
import LeanMarkupsafe.Proofs.Provenance

/-!
# The harness: one `Verified<Layer>` structure per layer

Each `Verified<Layer>` bundles a proof term for every headline property of
`Specifications/Basic.lean` that the layer claims. A specification with no
proof is a compile error the moment it needs a field here: you cannot
construct a `Verified<Layer>` value without every proof in hand. If a stated
specification turns out false, its slot's type flips to a refutation rather
than being dropped, so this file stays an honest map of what is verified.
-/

namespace LeanMarkupsafe

/-- Escaping and unescaping (`RepoImpl/Escape.lean`, `RepoImpl/Unescape.lean`). -/
structure VerifiedEscape where
  /-- `escape_sound`. -/
  escapeSound : Spec.escapeSound
  /-- `unescape_escape`. -/
  unescapeEscape : Spec.unescapeEscape
  /-- `escape_unescape`. -/
  escapeUnescape : Spec.escapeUnescape
  /-- `isEscaped_iff`. -/
  isEscapedIffImage : Spec.isEscapedIffImage
  /-- `escape_injective`. -/
  escapeInjective : Spec.escapeInjective
  /-- `escape_markup_id`. -/
  escapeMarkupId : Spec.escapeMarkupId
  /-- `escape_length`. -/
  escapeLength : Spec.escapeLength
  /-- `softStr_markup`. -/
  softStrMarkup : Spec.softStrMarkup
  /-- `escapeSilent_spec`. -/
  escapeSilent : Spec.escapeSilentSpec

theorem theVerifiedEscape : VerifiedEscape where
  escapeSound := escape_sound
  unescapeEscape := unescape_escape
  escapeUnescape := escape_unescape
  isEscapedIffImage := isEscaped_iff
  escapeInjective := escape_injective
  escapeMarkupId := escape_markup_id
  escapeLength := escape_length
  softStrMarkup := softStr_markup
  escapeSilent := escapeSilent_spec

/-- The invariant's closure under the `Markup` operations
(`RepoImpl/Escape.lean`, `RepoImpl/Format.lean`). -/
structure VerifiedClosure where
  /-- `concat_markup_markup`. -/
  appendClosed : Spec.appendClosed
  /-- `concat_escapes`. -/
  concatEscapes : Spec.concatEscapes
  /-- `concat_string_closed`. -/
  concatStringClosed : Spec.concatStringClosed
  /-- `join_closed`. -/
  joinClosed : Spec.joinClosed
  /-- `join_markup_closed`. -/
  joinMarkupClosed : Spec.joinMarkupClosed
  /-- `formatWith_closed`. -/
  formatWithClosed : Spec.formatWithClosed
  /-- `mod_closed`. -/
  modClosed : Spec.modClosed
  /-- `argsSafe_proof`. -/
  argsSafe : Spec.argsSafe

theorem theVerifiedClosure : VerifiedClosure where
  appendClosed := concat_markup_markup
  concatEscapes := concat_escapes
  concatStringClosed := concat_string_closed
  joinClosed := join_closed
  joinMarkupClosed := join_markup_closed
  formatWithClosed := formatWith_closed
  modClosed := mod_closed
  argsSafe := argsSafe_proof

/-- `striptags` (`RepoImpl/StripTags.lean`). -/
structure VerifiedStripTags where
  /-- `striptags_no_tags`. -/
  noTags : Spec.striptagsNoTags
  /-- `removeTags_no_lt`. -/
  noLt : Spec.removeTagsNoLt
  /-- `striptags_eq`. -/
  passes : Spec.striptagsEq

theorem theVerifiedStripTags : VerifiedStripTags where
  noTags := striptags_no_tags
  noLt := removeTags_no_lt
  passes := striptags_eq

/-- What `format` and `%` compute for any template, trusted HTML included
(`Proofs/Provenance.lean`). -/
structure VerifiedInterpolation where
  /-- `formatWith_interpolates`. -/
  formatWith : Spec.formatWithInterpolates
  /-- `format_interpolates`. -/
  format : Spec.formatInterpolates
  /-- `mod_tuple_interpolates`. -/
  modTuple : Spec.modTupleInterpolates
  /-- `mod_mapping_interpolates`. -/
  modMapping : Spec.modMappingInterpolates
  /-- `string_arg_rendering`. -/
  stringArg : Spec.stringArgRendering
  /-- `formatWith_strings`. -/
  formatWithStrings : Spec.formatWithStrings
  /-- `format_strings`. -/
  formatStrings : Spec.formatStrings
  /-- `format_keywords`. -/
  formatKeywords : Spec.formatKeywords

theorem theVerifiedInterpolation : VerifiedInterpolation where
  formatWith := formatWith_interpolates
  format := format_interpolates
  modTuple := mod_tuple_interpolates
  modMapping := mod_mapping_interpolates
  stringArg := string_arg_rendering
  formatWithStrings := formatWith_strings
  formatStrings := format_strings
  formatKeywords := format_keywords

/-- Execution: every operation that walks its input runs in place, and the
in-place implementation is the specified function (the `@[csimp]` lemmas in
`RepoImpl/`). -/
structure VerifiedExecution where
  /-- `escape_eq_fast`. -/
  escape : Spec.escapeRunsInPlace
  /-- `unescape_eq_fast`. -/
  unescape : Spec.unescapeRunsInPlace
  /-- `Markup.striptags_eq_fast`. -/
  striptags : Spec.striptagsRunsInPlace
  /-- `Markup.split_eq_fast`. -/
  split : Spec.splitRunsInPlace
  /-- `Markup.formatWith_eq_fast`. -/
  formatWith : Spec.formatWithRunsInPlace
  /-- `Markup.mod_eq_fast`. -/
  mod : Spec.modRunsInPlace
  /-- `Markup.joinMarkup_eq_fast`. -/
  join : Spec.joinRunsInPlace
  /-- `Markup.times_eq_fast`. -/
  times : Spec.timesRunsInPlace
  /-- `pyDigits_eq_fast`. -/
  pyDigits : Spec.pyDigitsRunsInPlace

theorem theVerifiedExecution : VerifiedExecution where
  escape := escape_eq_fast
  unescape := unescape_eq_fast
  striptags := Markup.striptags_eq_fast
  split := Markup.split_eq_fast
  formatWith := Markup.formatWith_eq_fast
  mod := Markup.mod_eq_fast
  join := Markup.joinMarkup_eq_fast
  times := Markup.times_eq_fast
  pyDigits := pyDigits_eq_fast

end LeanMarkupsafe
