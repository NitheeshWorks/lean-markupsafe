import LeanMarkupsafe.Proofs.Escape
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
  /-- `format_closed`. -/
  formatClosed : Spec.formatClosed
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
  formatClosed := format_closed
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

/-- Provenance of `format`/`%` output for any template, trusted HTML
included (`Proofs/Provenance.lean`). -/
structure VerifiedProvenance where
  /-- `format_provenance`. -/
  format : Spec.formatProvenance
  /-- `mod_provenance`. -/
  mod : Spec.modProvenance
  /-- `string_arg_rendering`. -/
  stringArg : Spec.stringArgRendering
  /-- `format_string_args_escaped`. -/
  formatStrings : Spec.formatStringArgsEscaped
  /-- `mod_string_args_escaped`. -/
  modStrings : Spec.modStringArgsEscaped

theorem theVerifiedProvenance : VerifiedProvenance where
  format := format_provenance
  mod := mod_provenance
  stringArg := string_arg_rendering
  formatStrings := format_string_args_escaped
  modStrings := mod_string_args_escaped

end LeanMarkupsafe
