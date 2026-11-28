import J6R52FreshExteriorWordsComputedShell
import J6R25PreparedSupplyRegistry

/-! The public exterior uses literal typed coordinates. Its emitted
unsigned words are built by a paid ripple counter from the traversal
index, not supplied as already validated address tapes. Only the
one shared centre/sample head is used by all sixty-four groups. -/
namespace J6R54PublicFamily
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul
open J6R15ModeCost J6R25PreparedSupply J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6R14ZeroMode
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11800000

def zeroOrdinal (w : ℕ) : Meter (Word w) :=
  let z := emitZeros w
  ⟨⟨z.result,(congrArg List.length (emitted_zeros_exact w).1).trans List.length_replicate⟩,z.steps+3⟩

theorem zero_ordinal_exact (w : ℕ) :
    (zeroOrdinal w).result.val=0 ∧ (zeroOrdinal w).steps=4*w+4 := by
  constructor
  · change bitsValue (emitZeros w).result=0
    rw [(emitted_zeros_exact w).1,value_zero]
  · change (emitZeros w).steps+3=_
    rw [(emitted_zeros_exact w).2]

def emitOrdinal (w : ℕ) : ℕ→Meter (Word w)
  | 0 => zeroOrdinal w
  | k+1 =>
    let a := emitOrdinal w k
    let b := increment a.result
    ⟨b.result,a.steps+b.steps+3⟩

def ordinalFee (w k : ℕ) : ℕ := 4*w+4+k*(13*w+7)

theorem emitted_ordinal_exact (w k : ℕ) (hw : 0<w) (fit : k<2^w) :
    (emitOrdinal w k).result.val=k ∧ (emitOrdinal w k).steps=ordinalFee w k := by
  induction k with
  | zero => simpa only [emitOrdinal,ordinalFee,Nat.zero_mul,Nat.add_zero] using zero_ordinal_exact w
  | succ k ih =>
    obtain ⟨value,fee⟩ := ih (Nat.lt_of_succ_lt fit)
    have fit' : (emitOrdinal w k).result.val+1<2^w := by rwa [value]
    obtain ⟨v,c⟩ := increment_exact hw _ fit'
    constructor
    · change (increment (emitOrdinal w k).result).result.val=_
      rw [v,value]
    · change (emitOrdinal w k).steps+(increment (emitOrdinal w k).result).steps+3=_
      rw [fee,c]
      simp only [ordinalFee,Nat.succ_mul]
      omega

structure QueryHead (tc tj tw : ℕ) where
  centre : Word tc
  sample : Word tj
  magnitude : Word tw

def emitQueryHead (tc tj tw : ℕ) (centre sample : ℕ) : Meter (QueryHead tc tj tw) :=
  let T := emitOrdinal tc centre
  let J := emitOrdinal tj sample
  let C := retainAtWidth tw T.result
  ⟨⟨T.result,J.result,C.result⟩,T.steps+J.steps+C.steps+6⟩

theorem emitted_query_head_exact {tc tj tw t j : ℕ} (ht : 0<tc) (hj : 0<tj)
    (fT : t<2^tc) (fJ : j<2^tj) (fW : t<2^tw) :
    let H := emitQueryHead tc tj tw t j
    H.result.centre.val=t ∧ H.result.sample.val=j ∧ H.result.magnitude.val=t ∧
      H.steps=ordinalFee tc t+ordinalFee tj j+(2*tc+4*tw+5)+6 := by
  obtain ⟨T,cT⟩ := emitted_ordinal_exact tc t ht fT
  obtain ⟨J,cJ⟩ := emitted_ordinal_exact tj j hj fJ
  obtain ⟨B,cB⟩ := retain_at_width_exact tw (emitOrdinal tc t).result (by rwa [T])
  refine ⟨T,J,B.trans T,?_⟩
  change (emitOrdinal tc t).steps+(emitOrdinal tj j).steps+
    (retainAtWidth tw (emitOrdinal tc t).result).steps+6=_
  rw [cT,cJ,cB]

def realAddress {tc tj tw : ℕ} (H : QueryHead tc tj tw) (g : Fin 64) :
    Meter (OccurrenceAddress tc tj) :=
  let G := emitOrdinal 6 g.val
  ⟨⟨H.centre,H.sample,G.result⟩,G.steps+3⟩

theorem real_address_exact {tc tj tw : ℕ} (H : QueryHead tc tj tw) (g : Fin 64) :
    let R := realAddress H g
    R.result.centre=H.centre ∧ R.result.sample=H.sample ∧ R.result.group.val=g.val ∧
      R.steps=ordinalFee 6 g.val+3 := by
  obtain ⟨G,cG⟩ := emitted_ordinal_exact 6 g.val (by decide) g.isLt
  exact ⟨rfl,rfl,G,congrArg (·+3) cG⟩

def signedContext {tc tj tw bw : ℕ} (H : QueryHead tc tj tw) (codeWord : Word bw) : CentreContext tw bw :=
  ⟨false,H.magnitude,codeWord⟩

theorem actual_signed_context {tc tj tw bw : ℕ} (H : QueryHead tc tj tw) (codeWord : Word bw) :
    (signedContext H codeWord).center=H.magnitude.val ∧
      (signedContext H codeWord).codeWidth=codeWord := ⟨rfl,rfl⟩

abbrev KeyWidth (kp tc tj : ℕ) : ℕ := kp+(tc+(tj+6))

def issueExterior {kp tc tj : ℕ} (mark : Word kp) (R : OccurrenceAddress tc tj) :
    Meter (Word (KeyWidth kp tc tj)) :=
  preparedKey mark R.centre R.sample R.group

theorem issued_exterior_exact {kp tc tj : ℕ} (mark : Word kp) (R : OccurrenceAddress tc tj) :
    (issueExterior mark R).result=joinKey mark (joinKey R.centre (joinKey R.sample R.group)) ∧
      (issueExterior mark R).steps=6*KeyWidth kp tc tj+10 :=
  prepared_key_exact mark R.centre R.sample R.group

theorem issued_exterior_equal_address {kp tc tj : ℕ} {mark : Word kp}
    {R R' : OccurrenceAddress tc tj}
    (eq : (issueExterior mark R).result=(issueExterior mark R').result) :
    R.centre=R'.centre ∧ R.sample=R'.sample ∧ R.group=R'.group :=
  (prepared_key_injective eq).2

#print axioms zero_ordinal_exact
#print axioms emitted_ordinal_exact
#print axioms emitted_query_head_exact
#print axioms real_address_exact
#print axioms actual_signed_context
#print axioms issued_exterior_exact
#print axioms issued_exterior_equal_address
end J6R54PublicFamily

