import P5AlwaysSatOriginalTaylorChart
import P5AlwaysSatOriginalPhysicalMAINBranch

/-! Genuine MAIN certificate to source numerical caps. The width-three
sparse order uses its own m_test and rho=n+1, not a four-clone degree. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainBalance P5MainIterator P5MainBalance.M6
open J1MainSourcePlacement J1MainSourceCollision
open DiagonalAbundance (Draw)
open scoped BigOperators Classical

section Geometry
variable {V X W F I B : Type*} [Fintype V] [Fintype X] [Fintype W] [Fintype I]
  [Fintype B] [LinearOrder B] [Nonempty B]
variable {o : X→W} {f : X→F} {pin : V↪X}
variable (C : MAINCertificate (I:=I) (S:=B) o f pin)

omit [Nonempty B] in
theorem certificate_layout_owners : C.layout.placement.owner=o := C.literal_owner
omit [Nonempty B] in
theorem certificate_layout_factors : C.layout.factor=f := C.literal_factor

omit [LinearOrder B] [Nonempty B] in
private theorem wordcell_draw_card :
    Fintype.card (WordCell I B)=Fintype.card (Draw I B) :=
  (Fintype.card_congr (mainCellEquiv I B)).symm

theorem certificate_caps_cell (u : WordCell I B) :
    cellLoad C.layout u*Fintype.card (WordCell I B)≤2*Fintype.card X := by
  let c := (mainCellEquiv I B).symm u
  have hc (e : X) : (C.layout.placement.slot e).2=u ↔ C.data.cell e=c := by
    change mainCellEquiv I B (C.data.cell e)=u ↔ C.data.cell e=c
    rw [←(mainCellEquiv I B).apply_symm_apply u]
    exact (mainCellEquiv I B).apply_eq_iff_eq
  have h : cellLoad C.layout u=SourceDensity.fiberCount C.data.cell c := by
    unfold cellLoad SourceDensity.fiberCount
    congr 1
    ext e
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hc e
  have hd : 0<(Fintype.card (Draw I B):ℚ) := by
    exact_mod_cast Fintype.card_pos (α:=Draw I B)
  have hh := C.cell_cap c
  rw [Paper5.HybridClosure.literal_load_is_fibre,←h] at hh
  have hn := (le_div_iff₀ hd).mp hh
  rw [wordcell_draw_card]
  exact_mod_cast hn

theorem certificate_caps_copies :
    Fintype.card (Fin (J1MainSourceBridge.copies C.data))*Fintype.card (WordCell I B)≤
      2*Fintype.card X := by
  rw [Fintype.card_fin,wordcell_draw_card]
  have hd : 0<(Fintype.card (Draw I B):ℚ) := by
    exact_mod_cast Fintype.card_pos (α:=Draw I B)
  exact_mod_cast (le_div_iff₀ hd).mp C.copy_cap
end Geometry

section Sizes
variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

noncomputable def mainN : ℕ := Fintype.card (Port E T)
noncomputable def directDegree : ℕ := Fintype.card (ClausePort E T)
noncomputable def sparseDegree : ℕ := 3*Fintype.card (CloneFactor E T)+6*mainN E T

theorem actual_direct_degree :
    directDegree E T=3*mainN E T-2 := by
  unfold directDegree mainN
  rw [port_card,cycle_slots_card]
  have hp := original_port_card E T
  omega

theorem literal_clone_variable_range [DecidableEq V] [Nonempty V]
    (hC : ∀ v,GraphCutMoments.degree E v=3) (hT : T.card≤Fintype.card V/4) :
    Fintype.card V≤mainN E T ∧ mainN E T≤9*Fintype.card V := by
  have hp := original_port_card E T
  have he := GraphCutMoments.regular_edge_count E 3 hC
  have hpos := Fintype.card_pos (α:=V)
  unfold mainN
  omega

theorem sparse_nominal_width_bound : sparseDegree E T ≤ 12*mainN E T := by
  have hf : Fintype.card (CloneFactor E T)=Fintype.card (Factor E T)+(cycleSlots E T).card := by
    rw [Fintype.card_sum,Fintype.card_coe]
  rw [cycle_slots_card] at hf
  have hb := factor_card E T
  have hp := original_port_card E T
  unfold sparseDegree mainN
  omega
end Sizes

#print axioms certificate_layout_owners
#print axioms certificate_layout_factors
#print axioms certificate_caps_cell
#print axioms certificate_caps_copies
#print axioms actual_direct_degree
#print axioms literal_clone_variable_range
#print axioms sparse_nominal_width_bound
end Paper5.AlwaysSatOriginal.Physical.Taylor