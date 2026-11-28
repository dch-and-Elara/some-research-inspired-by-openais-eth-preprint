import V8NativeMessageN6MainFiberWords

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14500000

/-! Close the zero measurement at the identical nativeScan address.
The nonempty E branch has a truly empty restricted word list in a
hit group. At E=U=empty the actual full jet contains a zero edge-OR
factor; this is not merely a constant coefficient or parity argument. -/
namespace V8NativeMessage.N6.MainFiber
open V8NativeMessage.C3.NativeAssembly.MainScan
open scoped BigOperators Classical Polynomial
open Polynomial

noncomputable section
variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J : ℕ}
variable (hreg : ∀ v,GraphCutMoments.degree F v=3)
variable (L : CloneTuple F r Q J)

omit [DecidableEq W] in
theorem theta_zero_word_no_correction (hU : L.U=∅) (f : Clause F) (v : Clone W) :
    θ L (fun _=>false) f v=0 := by
  simp [θ,hU]

theorem nativeScan_zero_restricted (hC : positiveCover L.frame)
    (h0 : zeroTarget L.frame) (hE : L.frame.E.Nonempty) (σ : W→Bool) :
    (nativeScan F hreg L σ).2.2=0 := by
  rw [native_value_uses_representatives F hreg L σ (zero_feasible _ h0)]
  obtain ⟨v,hv⟩ := hE
  let g := L.frame.group v
  apply Finset.prod_eq_zero (Finset.mem_univ g)
  apply Finset.sum_eq_zero
  intro x hx
  exact (((zero_eligible_iff L.frame hC h0 g x).1 (Finset.mem_filter.mp hx).2).2
    ⟨⟨v,rfl⟩,hv⟩).elim

theorem nativeScan_zero_edge_OR (hC : positiveCover L.frame)
    (h0 : zeroTarget L.frame) (hE : L.frame.E=∅) (hF : F.Nonempty) (σ : W→Bool) :
    (nativeScan F hreg L σ).2.2=0 := by
  let hf := zero_feasible _ h0
  rw [native_value_uses_representatives F hreg L σ hf]
  have hU : L.U=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun v hv=>by
    have hm := L.correction_subset hv
    rw [hE] at hm
    exact Finset.notMem_empty v hm)
  obtain ⟨e,he⟩ := hF
  let c : Clause F := .inr (.inl ⟨e,he⟩)
  let g := L.factorGroup c
  apply Finset.prod_eq_zero (Finset.mem_univ g)
  have hag : ¬touches L.frame g := fun ⟨v,hv⟩=>by
    rw [hE] at hv
    exact Finset.notMem_empty v.val hv
  calc
    _ = nativeGroup F hreg L σ g (merge L.frame (repWord L.frame hf) g (zeroWord L.frame g)) := by
      refine Finset.sum_eq_single (zeroWord L.frame g) ?_ ?_
      · intro x hx hn
        exact (hn ((zero_eligible_iff L.frame hC h0 g x).1 (Finset.mem_filter.mp hx).2).1).elim
      · intro hn
        exact (hn (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (zero_eligible_iff L.frame hC h0 g _).2 ⟨rfl,hag⟩⟩)).elim
    _ = 0 := by
      rw [zero_merge _ hC h0 hf]
      unfold nativeGroup
      have hc : c ∈ (Finset.univ : Finset (Clause F)).filter (fun a=>L.factorGroup a=g) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ c,rfl⟩
      apply Finset.prod_eq_zero hc
      simp [c,cloneFactor,theta_zero_word_no_correction L hU]

omit [DecidableEq W] in
theorem zero_global_eligible_iff_empty (hC : positiveCover L.frame)
    (h0 : zeroTarget L.frame) :
    (∃ x : Clone W→Bool,∀ g,eligible L.frame g (fun v=>x v.val)) ↔ L.frame.E=∅ := by
  constructor
  · rintro ⟨x,hx⟩
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    let g := L.frame.group v
    exact ((zero_eligible_iff L.frame hC h0 g _).1 (hx g)).2 ⟨⟨v,rfl⟩,hv⟩
  · intro he
    refine ⟨fun _=>false,fun g=>(zero_eligible_iff L.frame hC h0 g _).2 ⟨rfl,?_⟩⟩
    rintro ⟨v,hv⟩
    rw [he] at hv
    exact Finset.notMem_empty v.val hv

#print axioms theta_zero_word_no_correction
#print axioms nativeScan_zero_restricted
#print axioms nativeScan_zero_edge_OR
#print axioms zero_global_eligible_iff_empty
end
end V8NativeMessage.N6.MainFiber
