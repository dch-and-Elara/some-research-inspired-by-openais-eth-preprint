import P5HybridClosureD
import P5HybridClosureMain
import J6R11CollisionGreedy

/-! Pair counting for actual tagged physical ports, and the literal
rounded Appendix D packing for the specified exterior ties. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open J1MainSourceLabels J1MainSourceCollision DiagonalAbundance

section PairCounting
variable {E R C T : Type*} [Fintype E] [DecidableEq E]
  [DecidableEq R] [DecidableEq C] [DecidableEq T]

theorem bad_pairs_with_ties (t : C→Option T) (row : E→R) (col : E→C)
    (d₁ d₂ k n : ℕ)
    (hr : ∀ v, (varFibre row v).card≤d₁)
    (hc : ∀ v, (facFibre col v).card≤d₂)
    (ht : ∀ v, (tagFibre (t ∘ col) v).card≤k+1)
    (hn : (tiedSlots (t ∘ col)).card≤n) :
    (badPairs t row col).card ≤ (d₁+(d₂-1))*Fintype.card E+k*n := by
  let tag := t ∘ col
  let d := d₁+(d₂-1)
  have hf (e : E) : ((facFibre col (col e)).erase e).card≤d₂-1 := by
    have he : e∈facFibre col (col e) := by simp [facFibre]
    rw [Finset.card_erase_of_mem he]
    exact Nat.sub_le_sub_right (hc _) 1
  have hb (e : E) : (badNeighbors tag row col e).card ≤
      d+k*(if e∈tiedSlots tag then 1 else 0) := by
    have half : ((varFibre row (row e)) ∪ (facFibre col (col e)).erase e).card≤d :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add (hr _) (hf e))
    have hsum := (Finset.card_union_le
      ((varFibre row (row e)) ∪ (facFibre col (col e)).erase e)
      ((tag e).elim ∅ (fun v => (tagFibre tag v).erase e))).trans
      (Nat.add_le_add_right half _)
    change (badNeighbors tag row col e).card≤_ at hsum
    cases he : tag e with
    | none => simpa [tiedSlots,he] using hsum
    | some v =>
      have hv : e∈tagFibre tag v := by simp [tagFibre,he]
      have hcnt : ((tagFibre tag v).erase e).card≤k := by
        rw [Finset.card_erase_of_mem hv]
        have hv' := ht v
        change (tagFibre tag v).card≤k+1 at hv'
        omega
      rw [he,Option.elim_some] at hsum
      simpa [tiedSlots,he] using hsum.trans (Nat.add_le_add_left hcnt d)
  have hcard : (badPairs t row col).card=∑ e : E,(badNeighbors tag row col e).card := by
    have he : badPairs t row col =
        Finset.univ.filter (fun p : E×E => p.2∈badNeighbors tag row col p.1) := by
      ext p
      simpa [tag] using (bad_neighbor_exists t row col p.1 p.2)
    rw [he,Finset.card_filter,Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro e _
    have hh := Finset.card_filter (s:=(Finset.univ : Finset E)) (p:=fun q=>q∈badNeighbors tag row col e)
    rw [Finset.filter_univ_mem] at hh
    exact hh.symm
  have hs : (∑ e : E, if e∈tiedSlots tag then (1:ℕ) else 0)=(tiedSlots tag).card := by
    have h := Finset.card_filter (s:=(Finset.univ : Finset E)) (p:=fun e=>e∈tiedSlots tag)
    rw [Finset.filter_univ_mem] at h
    exact h.symm
  rw [hcard]
  calc
    _ ≤ ∑ e : E,(d+k*(if e∈tiedSlots tag then (1:ℕ) else 0)) :=
      Finset.sum_le_sum (fun e _ => hb e)
    _ = d*Fintype.card E+k*(tiedSlots tag).card := by
      rw [Finset.sum_add_distrib,←Finset.mul_sum,hs]
      simp [Nat.mul_comm]
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left k hn) _
end PairCounting

section DPhysical
open J6R10Repack J6R11CollisionReindex J6R11Collision P11FullPacking
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (cubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)

local notation "F" => replacedEdges E cubic
local notation "reg" => replaced_cubic E cubic loopless
local notation "N" => dNetwork F reg

abbrev DPrimitives (a : ℕ) := Primitive (MainClonedCNF.Port F) (DOld F) E (Fin a)

/-- D uses the factor-key side of the generic tied calculation for its old
vertices. This is the original cell map up to a canonical swap of sides. -/
noncomputable def dLabels {a : ℕ} (t : Fin a) (z : DPrimitives E cubic a→Fin 64) :
    Sample (DOld F) (MainClonedCNF.Port F) (Fin a→Fin 64) :=
  (factorWord t (exteriorTie E cubic) z,variableWord z)

theorem deviation_relabel {X C B : Type*} [Fintype X] [Fintype C] [Fintype B]
    (e : C≃B) (c : X→C) : deviation (e ∘ c)=deviation c := by
  have h (v : C) : load (e ∘ c) (e v)=load c v := by
    unfold load
    simp
  unfold deviation
  rw [←Equiv.sum_comp e,Fintype.card_congr e]
  simp only [h]

set_option maxHeartbeats 8000000 in
theorem expected_d_phi {a : ℕ} (t : Fin a) :
    mean (fun z : DPrimitives E cubic a→Fin 64 =>
      varianceScore (declaredCell N (dLabels E cubic t z).1 (dLabels E cubic t z).2)) ≤
      4*(Nat.card (DWire F):ℚ)+Fintype.card (TriVertex V) := by
  let T := exteriorTie E cubic
  have hcount := bad_pairs_with_ties T (N).col (N).row 2 3 1 (Fintype.card (TriVertex V))
    (fun v => by
      have hr := (d_subdivision_degree F reg v).le
      convert hr using 1
      congr 1
      ext q
      simp [varFibre]) (fun v => by
      have hr := d_old_degree F reg v
      convert hr using 1
      congr 1
      ext q
      simp [facFibre])
    (d_tied_fibre E cubic loopless) (d_tied_slots E cubic loopless).le
  have hp := expected_incidenceCost (S:=Fin 64) t T (N).col (N).row
  have hp' : mean (incidenceCost (S:=Fin 64) t T (N).col (N).row) ≤
      4*(Nat.card (DWire F):ℚ)+Fintype.card (TriVertex V) := by
    apply hp.trans
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (by simpa using hcount :
      (badPairs T (N).col (N).row).card≤4*Fintype.card (DWire F)+Fintype.card (TriVertex V))
  have hswap (z : DPrimitives E cubic a→Fin 64) :
    varianceScore (declaredCell N (dLabels E cubic t z).1 (dLabels E cubic t z).2) =
      incidenceCost t T (N).col (N).row z := by
    have hg := declared_variance_eq N (dLabels E cubic t z)
    have hrel := deviation_relabel (Equiv.prodComm (Fin a→Fin 64) (Fin a→Fin 64))
      (literalCell t T (N).col (N).row z)
    exact hg.trans hrel
  have hh := funext hswap
  rw [hh]
  exact hp'

set_option maxHeartbeats 2000000 in
theorem d_actual_tied_packing {a : ℕ} (t : Fin a) (Δ : ℕ) (hΔ : 3≤Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card (DWire F))
    (hslots : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card (DWire F)) :
    ∃ z : DPrimitives E cubic a→Fin 64, ∃ P : PhysicalPacking N a (Fin 64),
      (∀ p : TriVertex V, P.rowLabel (.inr (.inl p)) t =
        z (.inr (.inr ((exteriorPort E cubic).symm p).1))) ∧
      P.copies=ceilCopies (2^a) (maxFiber (declaredCell N P.rowLabel P.colLabel)) ∧
      varianceScore (declaredCell N P.rowLabel P.colLabel)≤2*(Nat.card (DWire F):ℚ)*Δ := by
  obtain ⟨z,hz⟩ := mean_le_select (fun z : DPrimitives E cubic a→Fin 64 =>
    varianceScore (declaredCell N (dLabels E cubic t z).1 (dLabels E cubic t z).2))
  have hp := hz.trans (expected_d_phi E cubic loopless t)
  have hm : (Nat.card (DWire F):ℚ)=24*(Fintype.card (TriVertex V):ℚ) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast d_physical_wire_count F reg
  have hp₁ : 4*(Nat.card (DWire F):ℚ)+Fintype.card (TriVertex V)≤
      6*(Nat.card (DWire F):ℚ) := by rw [hm]; linarith only [Nat.cast_nonneg (α:=ℚ) (Fintype.card (TriVertex V))]
  have hp₂ : 6*(Nat.card (DWire F):ℚ) ≤ 2*(Nat.card (DWire F):ℚ)*Δ := by
    have h : (3:ℚ)≤Δ := by exact_mod_cast hΔ
    have h' := mul_le_mul_of_nonneg_left h (show (0:ℚ)≤2*(Nat.card (DWire F):ℚ) by positivity)
    linarith only [h']
  obtain ⟨P,hrow,hcol,hcopy⟩ := actual_rounded_packing N (G:=Fin 64) (by simp)
    (dLabels E cubic t z).1 (dLabels E cubic t z).2 Δ (hp.trans (hp₁.trans hp₂)) hcollision hslots
  refine ⟨z,P,?_,?_,?_⟩
  · intro p
    rw [hrow]
    simp [dLabels,factorWord,factorKey,exteriorTie]
  · rw [hrow,hcol,hcopy]
  · rw [hrow,hcol]
    exact hp.trans (hp₁.trans hp₂)
end DPhysical

#print axioms bad_pairs_with_ties
#print axioms deviation_relabel
#print axioms expected_d_phi
#print axioms d_actual_tied_packing
end Paper5.HybridClosure