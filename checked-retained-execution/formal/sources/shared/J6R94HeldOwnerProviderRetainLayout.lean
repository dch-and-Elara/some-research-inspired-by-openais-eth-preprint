import J6R94HeldOwnerProviderHeaders

/-! Keep the already written complete label tape of the exact same
    paid R68 layout. Layout projection reproduces the old result;
    the new small pointer/record handoff charge is explicit. -/
namespace J6R94HeldOwnerProvider
open scoped Classical Polynomial
open AOracleMachineTime AOracleMachineTimeTape J6R10Repack P11FullPacking
open J6R11CollisionReindex J6R14LayoutCost J6R17ModeTape J6R68ActiveInputs
open V8NativeMessage.N2DLabels
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
set_option maxRecDepth 4400
set_option Elab.async false

structure KeptLayoutWords (a copies w edges : ℕ) where
  receipt : LayoutReceipt a copies w edges
  labels : List (List Bool)

/-- A view of the same outputs, not a second packed layout. -/
def KeptLayoutWords.rawView {a copies w edges : ℕ} (L : KeptLayoutWords a copies w edges) : GreedyPackedTape :=
  ⟨L.receipt.boxes,L.receipt.copies.bits,L.labels⟩

variable {E R C : Type*} [Fintype E] {a : ℕ} {N : Network E R C}
variable (I : Full64Input N a) (P : PhysicalPacking N a (Fin 64))
variable (q : ℕ) (hq : 0<q) (ha : a≤q)
variable (fit : Fintype.card E<2^q) (codec : ∀ w,I.format.label w=coordinateLabel w)
variable (caught : I.run.result.1=I.format.graph (fun v=>some (wordsOf P v)))
variable (rounded : RoundsExactly P) (W : Ingress I)

def paidSelectedSetupRetainingCompleteLabels :
    Meter (KeptLayoutWords a P.copies (q+1) (Fintype.card E)) :=
  let actual := runWithIngress I q W
  let h := fixed_export_of_same_paid_labels I P q hq ha fit codec caught rounded
  let x := ingress_run_is_actual_export I q W
  let receipt : LayoutReceipt a P.copies (q+1) (Fintype.card E) :=
    ⟨actual.result.boxes,⟨actual.result.copies,(congrArg List.length x.2.1).trans h.1⟩,
    by change bitsValue actual.result.copies=P.copies; rw [x.2.1]; exact h.2.1,
    x.1.symm ▸ h.2.2.1,x.1.symm ▸ h.2.2.2.1,x.1.symm ▸ h.2.2.2.2.1⟩
  ⟨⟨receipt,actual.result.vertexLabels⟩,actual.steps+4⟩

theorem retained_layout_has_unchanged_projection_and_one_layout_fee :
    let old := paidSelectedSetup I P q hq ha fit codec caught rounded W
    let keep := paidSelectedSetupRetainingCompleteLabels I P q hq ha fit codec caught rounded W
    keep.result.receipt=old.result ∧
      keep.result.labels=(runWithIngress I q W).result.vertexLabels ∧
      keep.steps=old.steps+4 := ⟨rfl,rfl,rfl⟩

theorem retained_layout_raw_view_is_the_same_actual_output :
    let kept := paidSelectedSetupRetainingCompleteLabels I P q hq ha fit codec caught rounded W
    kept.result.rawView=(runWithIngress I q W).result := by
  change (⟨(runWithIngress I q W).result.boxes,(runWithIngress I q W).result.copies,
    (runWithIngress I q W).result.vertexLabels⟩ : GreedyPackedTape)=(runWithIngress I q W).result
  cases (runWithIngress I q W).result
  rfl

def selectedLabelBits (labels : List (List Bool)) : ℕ := (labels.map List.length).sum

theorem kept_actual_label_bits_count_each_owner_once
    (selected : I.run.result.2=I.order.map (fun x=>I.format.label (wordsOf P x))) :
    let keep := paidSelectedSetupRetainingCompleteLabels I P q hq ha fit codec caught rounded W
    selectedLabelBits keep.result.labels=(6*a)*I.order.length := by
  change selectedLabelBits (runWithIngress I q W).result.vertexLabels=_
  rw [chosen_greedy_output_preserves_complete_vertex_words,selected]
  unfold selectedLabelBits
  simp only [List.map_map,Function.comp_def,codec,coordinateLabel_len]
  induction I.order with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one,ih,Nat.add_comm]

#print axioms retained_layout_has_unchanged_projection_and_one_layout_fee
#print axioms retained_layout_raw_view_is_the_same_actual_output
#print axioms kept_actual_label_bits_count_each_owner_once
end J6R94HeldOwnerProvider