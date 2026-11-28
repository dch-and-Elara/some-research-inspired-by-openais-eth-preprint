import J6R63OrdinalWholeValue
import J6R58OrdinalSpacePulse

/-! Selected word accounting at a genuine ranked emission. The observer
retains only the emitted exponent row and the current and incremented
ordinal words. This is an encoded-payload count, not an assertion that
the evaluator copies or allocates an observer byte string. -/
namespace J6R63Ordinal
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R49DFS J6R58OrdinalSpace
set_option autoImplicit false
set_option maxRecDepth 2800
set_option maxHeartbeats 5400000
set_option Elab.async false

variable {q n b : ℕ}

/-- The actual cursor transition erases any archival witness. This
relation starts at the same literal zero word used by runProbeRanked. -/
inductive ClockPrefix (start : Pending q n) : Pending q n → Word b → Prop where
  | initial : ClockPrefix start start (firstOrdinal b).result
  | next {p : Pending q n} {i : Word b} {raw : List (Word q)} {st : State q}
      (history : ClockPrefix start p i) (fired : p.pulse.result=.emit raw st) :
      ClockPrefix start (p.tail fired) (increment i).result

def ordinalObservedWords (p : Pending q n) (i : Word b) : Option (List Bool) :=
  match (numberedPulse p i).result with
  | .emit raw current _ next => some ((raw.flatMap Word.bits)++current.bits++next.bits)
  | _ => none

theorem physical_raw_word_count (raw : List (Word q)) :
    (raw.flatMap Word.bits).length=raw.length*q := by
  induction raw with
  | nil => simp
  | cons a raw ih =>
    simp only [List.flatMap_cons,List.length_append,a.size,ih,List.length_cons,Nat.succ_mul]
    rw [Nat.add_comm]

theorem genuine_ordinal_payload {p : Pending q n} {i : Word b} {raw : List (Word q)}
    {st : State q} (fired : p.pulse.result=.emit raw st) :
    let bits := (raw.flatMap Word.bits)++i.bits++(increment i).result.bits
    ordinalObservedWords p i=some bits ∧ bits.length=raw.length*q+2*b := by
  dsimp only
  refine ⟨?_,?_⟩
  · unfold ordinalObservedWords
    rw [one_actual_emission_carries_exactly_its_existing_word p i fired]
  · simp only [List.length_append,physical_raw_word_count,i.size,(increment i).result.size]
    omega

noncomputable section
variable {f : ℤ[X]} {ell s : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c}
variable (I : SiteTape sel d t q) (ordinal : NativeMenu (N sel) c t → ℕ)

theorem genuine_ranked_prefix_invariant (hq : 0<q) (hb : 0<b)
    (archive : HonestArchive I ordinal b) {first p : Pending q I.words.length} {i : Word b}
    (began : (startingCursor I hq).result=some first) (actual : ClockPrefix first p i) :
    SuffixFits I ordinal p i := by
  induction actual with
  | initial =>
    exact real_cursor_starts_with_checked_archival_rank I ordinal hq archive first began
  | @next p i raw st prev event ih =>
    exact ((native_paid_emit_law I ordinal hb).next p i raw st event ih).2

theorem real_ranked_site_observes_one_row_and_two_ordinal_words
    (hq : 0<q) (hb : 0<b) (archive : HonestArchive I ordinal b)
    {first p : Pending q I.words.length} {i : Word b}
    (began : (startingCursor I hq).result=some first) (actual : ClockPrefix first p i)
    {raw : List (Word q)} {st : State q} (fired : p.pulse.result=.emit raw st) :
    let bits := (raw.flatMap Word.bits)++i.bits++(increment i).result.bits
    ordinalObservedWords p i=some bits ∧ bits.length=I.words.length*q+2*b := by
  have fit := genuine_ranked_prefix_invariant I ordinal hq hb archive began actual
  obtain ⟨⟨β,_,row,_⟩,_⟩ := (native_paid_emit_law I ordinal hb).next p i raw st fired fit
  have hrow : raw.length=I.modes.length := by
    simpa only [List.length_map,vectorKey] using congrArg List.length row
  have hweight : I.words.length=I.modes.length := by
    simpa only [List.length_map] using congrArg List.length I.weightMeaning
  simpa only [hrow,hweight] using genuine_ordinal_payload (b:=b) fired

#print axioms ClockPrefix
#print axioms physical_raw_word_count
#print axioms genuine_ordinal_payload
#print axioms genuine_ranked_prefix_invariant
#print axioms real_ranked_site_observes_one_row_and_two_ordinal_words
end
end J6R63Ordinal
