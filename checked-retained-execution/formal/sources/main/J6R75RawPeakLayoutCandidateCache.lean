import J6R75RawPeakLayoutCandidateCurrent

/-! The only returned candidate state of the actual menu scan is a
fixed label/score entry. Retain its current comparison words while
charging the same candidate pair/tally workspace. No earlier pair
tape is put in the next candidate entry; this is a selected source
receipt, not a theorem about closure allocation or runtime GC. -/
namespace J6R75RawPeak
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionCandidate
open J6R12CollisionMenu

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4600
set_option maxHeartbeats 13900000
set_option Elab.async false

def layoutEntryWidth (x : Entry) : ℕ := x.label.length+x.score.length

theorem actual_candidate_cached_entry_keeps_two_fixed_words
    (w b : ℕ) (eval : List Bool→Meter (List Bool)) (best : Entry)
    (labels : List (List Bool)) (bestLabel : best.label.length=b) (bestScore : best.score.length=w)
    (each : ∀ x∈labels,x.length=b ∧ (eval x).result.length=w) :
    let ret := scanFrom w b eval best labels
    ret.result.label.length=b ∧ ret.result.score.length=w := by
  induction labels generalizing best with
  | nil=>exact ⟨bestLabel,bestScore⟩
  | cons next suffix ih=>
    let score := eval next
    let cond := compareBits score.result best.score
    let keep := if cond.result then ⟨next,score.result⟩ else best
    have dims : keep.label.length=b ∧ keep.score.length=w := by
      unfold keep
      split
      · exact each next List.mem_cons_self
      · exact ⟨bestLabel,bestScore⟩
    exact ih keep dims.1 dims.2 (fun x hx=>each x (List.mem_cons_of_mem _ hx))

section SourceFormat
variable {E R C A : Type*} [Fintype E] [Fintype A] [Nonempty A]

theorem one_actual_candidate_keeps_cached_control_words_in_the_pair_workspace
    (F : Format E R C A) (p : R⊕C→Option A) (v : R⊕C)
    (first : A) (pre : List A) (current : A) (post : List A)
    (resident roof : ℕ) (base : resident≤roof) :
    let eval := computeCandidate F.width F.kR F.kC F.b F.literals (F.graph p) (F.target v)
    let initial : Entry := ⟨F.label first,(eval (F.label first)).result⟩
    let before := scanFrom F.width F.b eval initial (pre.map F.label)
    let score := eval (F.label current)
    let compare := compareBits score.result before.result.score
    let now : Entry := ⟨F.label current,score.result⟩
    let keep := if compare.result then now else before.result
    let controlWords := layoutEntryWidth initial+layoutEntryWidth before.result+
      layoutEntryWidth now+layoutEntryWidth keep+1
    RealCandidateCall F.width F.b eval (F.label first) ((pre++current::post).map F.label) (F.label current) ∧
    controlWords=4*(F.b+F.width)+1 ∧
    ActualCandidateWorkspace F p v current (resident+controlWords) (roof+(4*(F.b+F.width)+1)) := by
  let eval := computeCandidate F.width F.kR F.kC F.b F.literals (F.graph p) (F.target v)
  let initial : Entry := ⟨F.label first,(eval (F.label first)).result⟩
  let before := scanFrom F.width F.b eval initial (pre.map F.label)
  let score := eval (F.label current)
  let compare := compareBits score.result before.result.score
  let now : Entry := ⟨F.label current,score.result⟩
  let keep := if compare.result then now else before.result
  have labelW (a : A) : (F.label a).length=F.b := encodeBits_length _ _
  have scoreW (a : A) : (eval (F.label a)).result.length=F.width := (F.candidate_exact p v a).1
  have old : before.result.label.length=F.b ∧ before.result.score.length=F.width := by
    exact actual_candidate_cached_entry_keeps_two_fixed_words F.width F.b eval initial
      (pre.map F.label) (labelW first) (scoreW first) (fun x hx=>by
        obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx
        exact ⟨labelW a,scoreW a⟩)
  have oldW : layoutEntryWidth before.result=F.b+F.width := by
    unfold layoutEntryWidth
    rw [old.1,old.2]
  have initW : layoutEntryWidth initial=F.b+F.width := congrArg₂ (·+·) (labelW first) (scoreW first)
  have hereW : layoutEntryWidth now=F.b+F.width := congrArg₂ (·+·) (labelW current) (scoreW current)
  have nextW : layoutEntryWidth keep=F.b+F.width := by
    unfold keep
    split
    · exact hereW
    · exact oldW
  have control :
      layoutEntryWidth initial+layoutEntryWidth before.result+layoutEntryWidth now+layoutEntryWidth keep+1=
      4*(F.b+F.width)+1 := by
    rw [initW,oldW,hereW,nextW]
    omega
  refine ⟨?_,control,true_candidate_materializes_real_pair_records_and_selected_tally_words F p v current
    _ _ (Nat.add_le_add base control.le)⟩
  refine Or.inr ⟨pre.map F.label,post.map F.label,by simp only [List.map_append,List.map_cons],?_⟩
  exact (congrArg (scanMenu F.width F.b eval (F.label first))
    (show (pre++current::post).map F.label=pre.map F.label++F.label current::post.map F.label by
      simp only [List.map_append,List.map_cons])).trans
    (actual_nonfirst_candidate_is_evaluated_after_that_precise_prefix F.width F.b eval
      (F.label first) (pre.map F.label) (F.label current) (post.map F.label))
end SourceFormat

#print axioms actual_candidate_cached_entry_keeps_two_fixed_words
#print axioms one_actual_candidate_keeps_cached_control_words_in_the_pair_workspace
end J6R75RawPeak
