import J6R21AncestorWhole
import J6R21LeafEnvelope

/-! Sum the measured source components without an arbitrary uniform
entry-fee premise. Absent work, including registration of the input
query tapes and active arithmetic, is not charged zero. Leaf-side
arithmetic is uniformly bounded from the actual schedule. -/
namespace J6R21Ancestor
open scoped BigOperators Polynomial Classical
open AOracleMachineTime A1R10 J6R19Retained
open J6ActiveRun J6R10Reachable J6R12Blueprint J6R11Blueprint
open J1PPrinted J6R16ModeCost J6R17ModeTape J6R21Leaf

variable {f : ℤ[X]} {ell s C : ℕ} (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell)) (hm : f.Monic)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

include cfg in
theorem every_call_precision_cap {c : Call (PhysicalHost f ell)}
    (R : NativeReach (Plan sel) r c) (sr : Stable s C r) (d0 : r.depth=0) (p0 : r.prec≤C*s) :
    c.prec≤precisionSize s C := by
  let Q (t : Call (PhysicalHost f ell)) :=
    NativeReach (Plan sel) r t ∧ t.prec≤precisionSize s C
  have hs : 0<s := cfg.constPos.trans_le cfg.constSmall
  have hB : r.prec≤precisionSize s C := by
    have H : C*s≤siteConstant C*(C*s) :=
      Nat.le_mul_of_pos_left _ (by unfold siteConstant; omega)
    exact p0.trans (H.trans (Nat.le_mul_of_pos_right _ hs))
  have one (x : Call (PhysicalHost f ell)) (hx : Q x) (w : (Plan sel).Slot x) :
      Q ((Plan sel).child x w) := by
    refine ⟨reach_snoc (Plan sel) hx.1 w,?_⟩
    change registerPrecision (S) x w.val.1≤precisionSize s C
    exact register_size_bound cfg sel hx.1 sr d0 p0 w.property w.val.1
  exact (nativeReach_run_invariant (Plan sel) Q one R ⟨.reflexive _,hB⟩).2

noncomputable def uniformLeafArithmetic :=
  polynomialLeafFee f.natDegree ell (precisionSize s C)
    (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)) (vertexCount r.host+4*r.edges) 0

include cfg in
theorem uniform_leaf_component (L : NativeLeafTapes sel r hm)
    (sr : Stable s C r) (d0 : r.depth=0) (p0 : r.prec≤C*s)
    (c : Call (PhysicalHost f ell)) :
    leafComponent sel r hm L (fun _ D=>D.run.steps) c ≤
      leafComponent sel r hm L (fun _ D=>D.directBill) c+uniformLeafArithmetic (C:=C) (s:=s) r := by
  classical
  by_cases H : NativeReach (Plan sel) r c
  · by_cases h : c.edges≤(S).cutoff
    · simp only [leafComponent,dif_pos H,dif_pos h]
      let D := L c H h
      have hE : D.fw.length≤f.natDegree := (size_of_monic_words D.hp hm D.modulus).le
      have hP := every_call_precision_cap cfg sel r H sr d0 p0
      have hV : D.nodes.length≤vertexCount r.host+4*r.edges :=
        (complete_vertex_list_length c.host D.nodes D.hn D.hall).trans_le (native_vertex_cap cfg sel H sr)
      change D.run.steps≤D.directBill+_
      rw [D.run_eq]
      exact concrete_leaf_arithmetic_envelope D.hp D.he D.hv D.nodes D.query
        hE (le_refl ell) hP h hV
    · simp [leafComponent,H,h]
  · simp [leafComponent,H]

theorem list_bill_add_uniform {X : Type*} (xs : List X) (a b : X→ℕ) (U : ℕ)
    (h : ∀ x,a x≤b x+U) :
    (xs.map a).sum≤(xs.map b).sum+xs.length*U := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := h x
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    rw [Nat.succ_mul xs.length]
    omega

include cfg in
theorem whole_mode_and_leaf_upper (L : NativeLeafTapes sel r hm)
    (root : Stable s C r) (d0 : r.depth=0) (p0 : r.prec≤C*s)
    (modeInputs : LayoutSupply (C:=C) sel r) :
    let H := pathLimit s C
    let T := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)
    let mode := ∑ j∈Finset.range H,((occurrences (Plan sel) r j).map
      (builtCallCost cfg sel root d0 p0 modeInputs)).sum
    let run := totalLeafComponent sel r hm L (fun _ D=>D.run.steps) H
    let exactEntries := totalLeafComponent sel r hm L (fun _ D=>D.directBill) H
    mode+run≤exactEntries+
      (H*comboFee s C+(H+1)*uniformLeafArithmetic (C:=C) (s:=s) r)*2^(prefixConstant C*T) := by
  let H := pathLimit s C
  let lam := Nat.clog 2 s
  let T := J9PrintedSchedule.leafThreshold s lam
  let A := uniformLeafArithmetic (C:=C) (s:=s) r
  let exponent := prefixConstant C*T
  let entryFee := totalLeafComponent sel r hm L (fun _ D=>D.directBill) H
  let leafFee := totalLeafComponent sel r hm L (fun _ D=>D.run.steps) H
  have counts : (∑ j∈Finset.range (H+1),(occurrences (Plan sel) r j).length)≤(H+1)*2^exponent := by
    apply (total_native_occurrences cfg sel root d0 p0).trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_right (by decide)
    exact compress_exponent s C cfg.constPos cfg.size (root_lambda_large cfg)
  have hFinite : leafFee≤entryFee+
      (∑ j∈Finset.range (H+1),(occurrences (Plan sel) r j).length)*A := by
    unfold leafFee entryFee totalLeafComponent
    rw [Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    exact list_bill_add_uniform _ _ _ _ (uniform_leaf_component cfg sel r hm L root d0 p0)
  have hLeaf' : leafFee≤entryFee+((H+1)*2^exponent)*A :=
    hFinite.trans (Nat.add_le_add_left (Nat.mul_le_mul_right A counts) _)
  have hMode := total_built_printed_rate cfg sel root d0 p0 modeInputs
  dsimp only
  have HH := Nat.add_le_add hMode hLeaf'
  change _≤entryFee+(H*comboFee s C+(H+1)*A)*2^exponent
  exact HH.trans_eq (by ring)

#print axioms every_call_precision_cap
#print axioms uniform_leaf_component
#print axioms whole_mode_and_leaf_upper
end J6R21Ancestor



