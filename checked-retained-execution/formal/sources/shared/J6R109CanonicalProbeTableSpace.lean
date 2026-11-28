import J6R109CanonicalProbeTableBits

/-! Concrete local pauses of the metered table builder. Count the
selected row payloads, counter/adder words and actual copied input
and output, not Lean allocator state or other algorithm phases. -/
namespace J6R109CanonicalProbeTable
open A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6R50RootIngress J6R49RootIngress J6R27PrescribedProbe J6R58ActivePrep

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 8500000

private theorem emit_row_count (e : ℕ) (one first : Word e) (n : ℕ) :
    (emitPositive e one first n).result.length=n := by
  induction n generalizing first with
  | zero=>rfl
  | succ n ih=>
    change ((addWord first one).result::(emitPositive e one (addWord first one).result n).result).length=n+1
    rw [List.length_cons,ih]

inductive CounterPause {e : ℕ} (one : Word e) :
    Word e → ℕ → List (Word e) → Word e → ℕ → Prop
  | start (cursor : Word e) (remaining : ℕ) : CounterPause one cursor remaining [] cursor remaining
  | pass (initial : Word e) (n : ℕ) (saved : List (Word e)) (now : Word e) (left : ℕ)
      (tail : CounterPause one (addWord initial one).result n saved now left) :
      CounterPause one initial (n+1) ((addWord initial one).result::saved) now left

theorem real_counter_pause_keeps_its_actual_prefix_and_suffix {e n left : ℕ}
    {one start now : Word e} {saved : List (Word e)} (cut : CounterPause one start n saved now left) :
    (emitPositive e one start n).result=saved++(emitPositive e one now left).result ∧
    saved.length+left=n := by
  induction cut with
  | start=>simp
  | pass initial k savedHere cursor left back ih=>
    constructor
    · change (addWord initial one).result::(emitPositive e one (addWord initial one).result k).result=
        (addWord initial one).result::(savedHere++(emitPositive e one cursor left).result)
      exact congrArg ((addWord initial one).result::·) ih.1
    · rw [List.length_cons]
      omega

def selectedEmitPayload (e left : ℕ) (saved : List (Word e)) (now : Word e) : ℕ :=
  let one := wordOne e
  let suffix := emitPositive e one now left
  let pending := addWord now one
  let pairs := now.val.zip one.val
  (wordAt e 0).val.length+rawPayload (saved.map Subtype.val)+
    rawPayload (suffix.result.map Subtype.val)+
    (encoded e 0).val.length+now.val.length+one.val.length+pending.result.val.length+
    2*pairs.length+(pairs.length+1)

theorem real_binary_counter_pause_has_selected_workspace (e d left : ℕ)
    (saved : List (Word e)) (now : Word e)
    (_active : 0<left)
    (cut : CounterPause (wordOne e) (encoded e 0) d saved now left) :
    let pairTape := now.val.zip (wordOne e).val
    (indexTape e (d+1)).result=
      wordAt e 0::(saved++(emitPositive e (wordOne e) now left).result) ∧
    (addWord now (wordOne e)).result.val=(addCore false pairTape).result.1 ∧
    selectedEmitPayload e left saved now≤e*(d+1)+7*e+1 := by
  obtain ⟨rows,parts⟩ := real_counter_pause_keeps_its_actual_prefix_and_suffix cut
  refine ⟨congrArg (wordAt e 0::·) rows,rfl,?_⟩
  have aligned : e*saved.length+e*left=e*d := by rw [←Nat.mul_add,parts]
  unfold selectedEmitPayload
  dsimp only
  rw [word_payload_exact,word_payload_exact,emit_row_count,
    (wordAt e 0).property,(encoded e 0).property,now.property,(wordOne e).property,
    (addWord now (wordOne e)).result.property,List.length_zip,now.property,(wordOne e).property,min_self,
    Nat.mul_add,Nat.mul_one]
  omega

def selectedCopyPayload {e : ℕ} (all pre : List (Word e)) (head : Word e) (post : List (Word e))
    (offset : ℕ) : ℕ :=
  let saved := pre.map (fun w=>(copyBits w.val).result)
  let pending := copyBits head.val
  let suffix := writeCoefficientRows post
  rawPayload (all.map Subtype.val)+rawPayload saved+pending.result.length+
    rawPayload suffix.result+(pending.result.take offset).length

private theorem actual_saved_words {e : ℕ} (xs : List (Word e)) :
    (xs.map fun w=>(copyBits w.val).result)=xs.map Subtype.val := by
  apply List.map_congr_left
  intro w _
  rw [copy_bits_exact]

theorem real_coefficient_copy_retains_one_input_and_output_prefix (e d offset : ℕ)
    (pre : List (Word e)) (head : Word e) (post : List (Word e))
    (cut : (indexTape e (d+1)).result=pre++head::post) :
    let previous := pre.map (fun w=>(copyBits w.val).result)
    let now := copyBits head.val
    let after := writeCoefficientRows post
    (canonicalTable e (d+1)).result=previous++now.result::after.result ∧
    selectedCopyPayload (indexTape e (d+1)).result pre head post offset≤2*(e*(d+1))+e := by
  let T := indexTape e (d+1)
  have len : T.result.length=d+1 := by
    change (wordAt e 0::(emitPositive e (wordOne e) (encoded e 0) d).result).length=d+1
    rw [List.length_cons,emit_row_count]
  have pieces : pre.length+1+post.length=d+1 := by
    rw [cut,List.length_append,List.length_cons] at len
    omega
  constructor
  · change (writeCoefficientRows T.result).result=_
    rw [actual_coefficient_row_writer_exact,show T.result=_ from cut,List.map_append,List.map_cons,
      actual_saved_words,copy_bits_exact,actual_coefficient_row_writer_exact]
  · change selectedCopyPayload T.result pre head post offset≤_
    have little : (head.val.take offset).length≤e := by
      rw [List.length_take,head.property]
      exact Nat.min_le_right _ _
    unfold selectedCopyPayload
    dsimp only
    rw [actual_saved_words,word_payload_exact,word_payload_exact,len,
      copy_bits_exact,head.property,actual_coefficient_row_writer_exact]
    dsimp only
    rw [word_payload_exact]
    have fold : e*pre.length+e+e*post.length=e*(d+1) := by
      calc
        e*pre.length+e+e*post.length=e*(pre.length+1+post.length) := by
          simp only [Nat.mul_add,Nat.mul_one]
        _=e*(d+1) := congrArg (e*·) pieces
    omega

def selectedBuilderRoof (e n : ℕ) : ℕ := max (e*n+7*e+1) (2*(e*n)+e)

/-- A maximum of the named source counter and table-copy phases. The
full retained table is real; the two stages' scratch is not added. -/
theorem actual_probe_table_has_a_single_selected_local_peak (e d : ℕ) :
    (∀ left saved now,0<left→CounterPause (wordOne e) (encoded e 0) d saved now left→
      selectedEmitPayload e left saved now≤selectedBuilderRoof e (d+1)) ∧
    (∀ offset pre head post,(indexTape e (d+1)).result=pre++head::post →
      selectedCopyPayload (indexTape e (d+1)).result pre head post offset≤selectedBuilderRoof e (d+1)) := by
  exact ⟨fun left saved now h C=>
      (real_binary_counter_pause_has_selected_workspace e d left saved now h C).2.2.trans (Nat.le_max_left _ _),
    fun offset pre head post C=>
      (real_coefficient_copy_retains_one_input_and_output_prefix e d offset pre head post C).2.trans
        (Nat.le_max_right _ _)⟩

#print axioms real_counter_pause_keeps_its_actual_prefix_and_suffix
#print axioms real_binary_counter_pause_has_selected_workspace
#print axioms real_coefficient_copy_retains_one_input_and_output_prefix
#print axioms actual_probe_table_has_a_single_selected_local_peak
end J6R109CanonicalProbeTable
