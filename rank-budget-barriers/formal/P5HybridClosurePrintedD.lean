import P5HybridClosureEnd
import P5HybridClosurePrintedMain
import J1PPrintedMesh
import HermiteLossSchedule

/-! Literal Appendix D tuning of the same cloned §8 CNF. The size
parameter is the printed s=n+m, with 4N variables and 5N+|E_G| clauses.
Unlike a mesh placeholder, this proof uses that exact size. -/
namespace Paper5.HybridClosure.Printed
open scoped Topology
open Filter J1PPrinted J9PrintedSchedule

def dSize (N : ℕ) : ℕ := 9*N+3*N/2
def dLambda (N : ℕ) : ℕ := Nat.clog 2 (dSize N)
def dU (N : ℕ) : ℕ := rootU (dLambda N)
def dA (N : ℕ) : ℕ := rootA (dLambda N)
def dL (N : ℕ) : ℕ := 2^(dA N)
def dCells (N : ℕ) : ℕ := arrayCard (dA N)
noncomputable def dDelta (N : ℕ) : ℕ := sourceDelta (dSize N)

theorem cloned_clause_count {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (V×V)) (left right : F→Fin 4) (σ : V→Bool) :
    (MainClonedCNF.formula F left right σ).length=5*Fintype.card V+F.card := by
  have hc (l : List V) : (l.flatMap MainClonedCNF.cycle).length = 4*l.length := by
    induction l with
    | nil => rfl
    | cons v l ih =>
      simp only [List.flatMap_cons,List.length_append,List.length_cons,ih]
      have h : (MainClonedCNF.cycle v).length=4 := rfl
      rw [h]
      omega
  unfold MainClonedCNF.formula
  rw [List.length_append,List.length_append,hc]
  simp
  omega

theorem d_size_is_cloned {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (V×V)) (reg : ∀v,GraphCutMoments.degree F v=3)
    (σ : V→Bool) :
    Fintype.card (Clone V)+(MainClonedCNF.formula F (MainClonedCNF.leftSlot F reg)
      (MainClonedCNF.rightSlot F reg) σ).length=dSize (Fintype.card V) := by
  rw [cloned_clause_count,Fintype.card_prod,Fintype.card_fin]
  have h := GraphCutMoments.regular_edge_count F 3 reg
  unfold dSize
  omega

theorem d_size_bounds (N : ℕ) : N≤dSize N ∧ dSize N≤11*N := by unfold dSize; omega

theorem d_widths (N : ℕ) : stepA (dLambda N) 0=dA N ∧ dU N≤dA N := by
  have h : stepA (dLambda N) 0=2*dU N := by
    simp [stepA,stepU_as_div,dU]
  refine ⟨h,?_⟩
  unfold dA rootA dU
  omega

def retainedEmbed (N : ℕ) : Fin (dU N) ↪ Fin (dA N) :=
  ⟨Fin.castLE (d_widths N).2,fun _ _ h=>Fin.ext (congrArg (fun v : Fin (dA N)=>v.val) h)⟩

def retainedCoordinates (N : ℕ) : Finset (Fin (dA N)) :=
  Finset.univ.map (retainedEmbed N)

theorem retained_card (N : ℕ) : (retainedCoordinates N).card=dU N := by
  rw [retainedCoordinates,Finset.card_map,Finset.card_univ,Fintype.card_fin]

theorem retained_level {N : ℕ} {i : Fin (dA N)} :
    i∈retainedCoordinates N↔i.val<dU N := by
  unfold retainedCoordinates
  constructor
  · intro hi
    obtain ⟨j,_,hj⟩ := Finset.mem_map.mp hi
    have he := congrArg Fin.val hj
    change j.val=i.val at he
    exact he ▸ j.isLt
  · intro hi
    exact Finset.mem_map.mpr ⟨⟨i.val,hi⟩,Finset.mem_univ _,Fin.ext rfl⟩

theorem retained_has_actual_center {N : ℕ} (hN : 0<N) (i : retainedCoordinates N) :
    ∃ t : ℤ, t∈HermiteLoss.retained (dA N) (dU N) (HermiteLoss.sourceH (24*N) (dU N)) ∧
      HermiteLoss.level t=i.val.val := by
  let v := i.val.val
  let t := P1DyadicGrid.pow₂ v
  let h := HermiteLoss.sourceH (24*N) (dU N)
  have hv : v<dU N := retained_level.mp i.property
  have hR : 0<dU N := Nat.zero_lt_of_lt hv
  have ht : 0<t := P1DyadicGrid.pow₂_pos v
  have ht₁ : t<P1DyadicGrid.pow₂ (dA N) := by
    exact pow_lt_pow_right₀ (by decide : (1:ℤ)<2) (hv.trans_le (d_widths N).2)
  have hl : HermiteLoss.level t=v := by
    simpa [t,HermiteLoss.level] using
      P1DyadicGrid.valuation_pow₂_mul_odd v (by decide : Odd (1:ℤ))
  have hp : 0<h := by
    have hc := HermiteLoss.h_cover (24*N) (dU N) hR
    change 3*(24*N)≤h*dU N at hc
    by_contra! hn
    have he : h=0 := by omega
    rw [he,zero_mul] at hc
    omega
  refine ⟨t,HermiteLoss.retained_mem.mpr ⟨P1DyadicGrid.mem_grid.mpr ⟨?_,ht₁⟩,ht.ne',?_⟩,hl⟩
  · have h := P1DyadicGrid.pow₂_pos (dA N)
    linarith only [h,ht]
  · rw [hl]
    exact (HermiteLoss.nonzero_node_active _ _ _ hp).mpr hv

/-- There are no other group coordinates among the actual active root
centers: the taper's strictly positive multiplicity forces level < u. -/
theorem actual_center_uses_retained {N : ℕ} {t : ℤ}
    (active : t∈HermiteLoss.retained (dA N) (dU N) (HermiteLoss.sourceH (24*N) (dU N))) :
    ∃ i : retainedCoordinates N, i.val.val=HermiteLoss.level t := by
  have hp := (HermiteLoss.retained_mem.mp active).2.2
  have hl : HermiteLoss.level t<dU N := by
    by_contra! hn
    simp [HermiteLoss.taper,Nat.sub_eq_zero_of_le hn] at hp
  let j : Fin (dA N) := ⟨HermiteLoss.level t,hl.trans_le (d_widths N).2⟩
  exact ⟨⟨j,retained_level.mpr hl⟩,rfl⟩

private theorem next_leaf_le_size (s d : ℕ) (hd : 0<d) :
    (s+d-1)/d≤s := by
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul hd).2
  have h : s ≤ s*d := by simpa using Nat.mul_le_mul_left s (show 1≤d by omega)
  rw [show (s+1)*d=s*d+d by ring]
  omega

theorem d_printed_feasible (N : ℕ) (hN : 0<N) (hd : 131072≤dLambda N) :
    leafThreshold (dSize N) (dLambda N)<24*N ∧ 0<dU N ∧ 3≤dDelta N ∧
    2*(dCells N)^2*dDelta N≤24*N ∧ dL N*dCells N≤24*N ∧ 2*dL N≤dDelta N := by
  have hu : 1≤dU N := by change 1≤dLambda N/131072; omega
  have hS := (d_size_bounds N).2
  have hlo : leafThreshold (dSize N) (dLambda N)<24*N :=
    (next_leaf_le_size _ _ (Nat.sqrt_pos.mpr (by omega))).trans_lt (by omega)
  have hf := source_packing_conditions (dSize N) (24*N) 0 hu hlo
  change 2*(stepD (dLambda N) 0)^2*dDelta N≤24*N ∧
    stepL (dLambda N) 0*stepD (dLambda N) 0≤24*N ∧ 2*stepL (dLambda N) 0≤dDelta N at hf
  unfold stepD stepL at hf
  rw [(d_widths N).1] at hf
  have hfinal : 2*(dCells N)^2*dDelta N≤24*N ∧
      dL N*dCells N≤24*N ∧ 2*dL N≤dDelta N := hf
  have hl : 4≤dL N := by
    have ha : 2≤dA N := by change 2≤2*dU N; omega
    exact Nat.pow_le_pow_right (show 0<(2:ℕ) by decide) ha
  have hdeg := hfinal.2.2
  exact ⟨hlo,hu,by omega,hfinal⟩

theorem d_printed_eventual :
    ∀ᶠ N : ℕ in atTop,
      leafThreshold (dSize N) (dLambda N)<24*N ∧ 0<dU N ∧ 3≤dDelta N ∧
      2*(dCells N)^2*dDelta N≤24*N ∧ dL N*dCells N≤24*N ∧ 2*dL N≤dDelta N := by
  have hclog : Tendsto (Nat.clog 2) atTop atTop := by
    simpa only [one_mul,add_zero] using clog_linear_tendsto 1 0 (by decide)
  filter_upwards [eventually_gt_atTop (0:ℕ),hclog.eventually (eventually_ge_atTop 131072)] with N hN hlog
  exact d_printed_feasible N hN (hlog.trans (Nat.clog_mono_right 2 (d_size_bounds N).1))

#print axioms cloned_clause_count
#print axioms d_size_is_cloned
#print axioms retained_card
#print axioms retained_level
#print axioms retained_has_actual_center
#print axioms actual_center_uses_retained
#print axioms d_printed_feasible
#print axioms d_printed_eventual
end Paper5.HybridClosure.Printed