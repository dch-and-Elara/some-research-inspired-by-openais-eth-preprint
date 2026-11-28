import J6R48GeneratedAddons
import J6R51PeakSidecar

/-! Named raw payload at the real emitter's row boundaries. The
metered equality is about the original recursion, not a substitute
that would precompute the full list before starting. -/
namespace J6R54PeakInput
open AOracleMachineTime J6R15ModeCost J6R36ChildFramedRoute J6R48GeneratedAddons J6R51Peak

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 13500000

variable {owner a key prec page : ℕ} {A : Type*}
local notation "Raw" => Addon owner a key prec page

def readAndCopyRawHead (readRow : A→Meter Raw) (x : A) : Meter Raw :=
  let got := readRow x
  let copied := copyAddon got.result
  ⟨copied.result,got.steps+copied.steps⟩

def resumeSiblingRawHeads (paid : List (Meter Raw)) (tail : Meter (List Raw)) : Meter (List Raw) :=
  paid.foldr (fun head prior=>⟨head.result::prior.result,head.steps+prior.steps+4⟩) tail

theorem actual_emit_resumes_from_its_copied_heads (readRow : A→Meter Raw)
    (before after : List A) :
    emit readRow (before++after)=
      resumeSiblingRawHeads (before.map (readAndCopyRawHead readRow)) (emit readRow after) := by
  induction before with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,List.map_cons,emit,resumeSiblingRawHeads,List.foldr_cons,readAndCopyRawHead] at *
    rw [ih]

theorem named_saved_heads_are_the_same_emitted_prefix (readRow : A→Meter Raw)
    (before after : List A) :
    ((emit readRow (before++after)).result.take before.length)=
      before.map (fun x=>(readAndCopyRawHead readRow x).result) := by
  induction before with
  | nil => rfl
  | cons x xs ih =>
    simp [emit,readAndCopyRawHead,ih]

theorem selected_emitter_prefix_bits_fit (readRow : A→Meter Raw)
    (before after : List A) :
    (((emit readRow (before++after)).result.take before.length).flatMap addonWords).length≤
      before.length*addonCap owner a key prec page := by
  rw [named_saved_heads_are_the_same_emitted_prefix]
  have size := flat_words_bound (before.map (fun x=>(readAndCopyRawHead readRow x).result))
    addonWords (addonCap owner a key prec page) (fun x _=>literal_addon_word_cap x)
  rw [List.length_map] at size
  exact size

#print axioms actual_emit_resumes_from_its_copied_heads
#print axioms named_saved_heads_are_the_same_emitted_prefix
#print axioms selected_emitter_prefix_bits_fit
end J6R54PeakInput
