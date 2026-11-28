import J6R16SpecializedBoxSelected
import J6R12BlueprintReach

/-! v9 J8 lines 807–809: the *full receiving precision* plus one
fits the actual printed probe address type at a duly sized root.
This is distinct from, and not needed by, the 10M-bit receiver. -/
namespace J8R64
open Polynomial J1PPrinted J6ActiveSchedule J6ActiveRun J6R12Blueprint J6R11Blueprint
open J6R11Repack J6R14SpecializedBox P1DyadicGrid
open scoped Polynomial
set_option autoImplicit false
set_option linter.unusedSectionVars false

private theorem packet_dominates_local_cost_shift (j : ℕ) :
    8*((j+7)+1)+2 ≤ (2:ℕ)^(j+7) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show j+1+7=j+7+1 by omega,pow_succ]
    omega

theorem packet_dominates_local_cost (a : ℕ) (ha : 7≤a) :
    8*(a+1)+2≤(2:ℕ)^a := by
  have rel : a-7+7=a := by omega
  simpa only [rel] using packet_dominates_local_cost_shift (a-7)

/-- Uniform finite inequality. At an odd centre this is the exact largest
precision among the centres. In fact the same upper bound works at all
centres using the printed lattice's D_t≤L. -/
theorem full_precision_fits_of_bounded_creation
    (p a M u : ℕ) (t : ℤ) (hp : p≤M) (ha : 7≤a) (hu : 32≤u) (huM : u≤M) :
    childPrecision p a M u t + 1 ≤ J9PrintedSchedule.probeCount M (2^a) := by
  let L : ℕ := 2^a
  have localCost := packet_dominates_local_cost a ha
  have hHeight : 8*height M u≤M := by
    have h := (height_bounds M u (by omega) huM).2
    have lift : height M u*32≤4*M := (Nat.mul_le_mul_left _ hu).trans h
    omega
  have hD : L / 2^(padicValInt 2 t)≤L := Nat.div_le_self _ _
  have hTail : 8*M*(a+1)≤M*(L-2) := by
    calc
      8*M*(a+1) = M*(8*(a+1)) := by ring
      _ ≤ M*(L-2) := Nat.mul_le_mul_left M (by change 8*(a+1)≤(2:ℕ)^a-2; omega)
  have hRoom : 1+L+(L-2)=2*L-1 := by
    change 8*(a+1)+2≤L at localCost
    omega
  unfold childPrecision J9PrintedSchedule.precision J9PrintedSchedule.probeCount J9PrintedSchedule.degreeBound
  apply Nat.add_le_add_right
  change p + 8*height M u*(L / 2^(padicValInt 2 t)) + 8*M*(a+1) ≤ M*(2*L-1)
  calc
    _ ≤ M + M*L + M*(L-2) := Nat.add_le_add
      (Nat.add_le_add hp (Nat.mul_le_mul hHeight hD)) hTail
    _ = M*(1+L+(L-2)) := by ring
    _ = _ := by rw [hRoom]

theorem root_parameters_force_large_taper {f : ℤ[X]} {s C : ℕ}
    (cfg : RootBounds s C f) : 32≤stepU (Nat.clog 2 s) 0 := by
  have h : 32*epsDen≤(2*epsDen)^30 := by
    calc
      _ ≤ (2*epsDen)^2 := by decide
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by decide)
  have hc : 0<C^10 := Nat.pow_pos cfg.constPos
  have below : 32*epsDen≤Nat.clog 2 s :=
    h.trans ((Nat.le_mul_of_pos_right _ hc).trans cfg.size)
  unfold stepU
  rw [pow_zero,Nat.mul_one]
  exact (Nat.le_div_iff_mul_le (by decide : 0<epsDen)).2 below

theorem root_parameters_exact_packet_bits (lam : ℕ) :
    stepA lam 0 = 2*stepU lam 0 := by
  simp [stepA]

variable {f : ℤ[X]} {ell s C : ℕ}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem actual_odd_root_precision_formula
    (r : Call (PhysicalHost f ell)) (t : Center S r) (ho : Odd t.val) :
    registerPrecision S r t =
      r.prec + 8 * height r.edges (stepU (Nat.clog 2 s) r.depth) *
        2^(stepA (Nat.clog 2 s) r.depth) + 8*r.edges*(stepA (Nat.clog 2 s) r.depth+1) := by
  change childPrecision r.prec (stepA (Nat.clog 2 s) r.depth) r.edges
    (stepU (Nat.clog 2 s) r.depth) t.val = _
  rw [childPrecision,odd_valuation_zero ho,pow_zero,Nat.div_one]
  rfl

theorem actual_printed_root_full_precision_fits
    (cfg : RootBounds s C f) (r : Call (PhysicalHost f ell))
    (t : Center S r) (root : r.depth=0) (hprec : r.prec≤r.edges)
    (huM : stepU (Nat.clog 2 s) 0≤r.edges) :
    registerPrecision S r t + 1 ≤ Fintype.card (Probe S r) := by
  rw [Fintype.card_fin]
  change childPrecision r.prec (stepA (Nat.clog 2 s) r.depth) r.edges
    (stepU (Nat.clog 2 s) r.depth) t.val + 1 ≤
      J9PrintedSchedule.probeCount r.edges (2^(stepA (Nat.clog 2 s) r.depth))
  set z : ℤ := t.val
  rw [root]
  have hu := root_parameters_force_large_taper cfg
  have ha : 7≤stepA (Nat.clog 2 s) 0 := by rw [root_parameters_exact_packet_bits]; omega
  exact full_precision_fits_of_bounded_creation _ _ _ _ _ hprec ha hu huM

theorem actual_printed_four_clone_full_precision_fits
    (cfg : RootBounds s C f) (r : Call (PhysicalHost f ell))
    (t : Center S r) (root : r.depth=0) (N : ℕ) (hn : 0<N)
    (hM : r.edges=24*N) (hprec : r.prec=4*N+1)
    (huM : stepU (Nat.clog 2 s) 0≤r.edges) :
    registerPrecision S r t + 1 ≤ Fintype.card (Probe S r) :=
  actual_printed_root_full_precision_fits cfg r t root (by omega) huM

theorem full_precision_selection_exists
    (cfg : RootBounds s C f) (r : Call (PhysicalHost f ell))
    (t : Center S r) (root : r.depth=0) (hprec : r.prec≤r.edges)
    (huM : stepU (Nat.clog 2 s) 0≤r.edges) :
    Nonempty (Fin (registerPrecision S r t+1) ↪ Probe S r) := by
  have b := actual_printed_root_full_precision_fits cfg r t root hprec huM
  rw [Fintype.card_fin] at b
  exact ⟨Fin.castLEEmb b⟩

/-- The general ready notion only requires old entry tags ≤ the current
working precision. Increasing the latter keeps the very same host and
graph admissible; it is not a legal way to claim the original P0 cap. -/
def raiseWorkingPrecision (r : Call (PhysicalHost f ell)) (p : ℕ) :
    Call (PhysicalHost f ell) := {r with prec:=p}

theorem raising_keeps_stable (r : Call (PhysicalHost f ell)) (p : ℕ) (hp : r.prec≤p)
    (seed : Stable s C r) : Stable s C (raiseWorkingPrecision r p) :=
  ⟨seed.edgeCount,seed.degree,fun j => (seed.tags j).trans hp,seed.sizeByDepth⟩

theorem raising_keeps_ready (r : Call (PhysicalHost f ell)) (p : ℕ) (hp : r.prec≤p)
    (rd : Ready S (sourceDelta s) r) : Ready S (sourceDelta s) (raiseWorkingPrecision r p) :=
  ⟨rd.active,rd.edgeCount,rd.degree,fun j => (rd.tags j).trans hp,
    rd.collision,rd.paddedSlots,rd.packetDegree,rd.widthFits,rd.fit⟩

/-- A concrete obstruction to dropping the original root cap. On the
same ready, stable host one can make the working precision too large
to have p_t+1 distinct original printed addresses. -/
theorem ready_stable_alone_does_not_supply_high_roster
    (r : Call (PhysicalHost f ell)) (t : Center S r)
    (rd : Ready S (sourceDelta s) r) (seed : Stable s C r) :
    let b := J9PrintedSchedule.degreeBound r.edges (2^(S).levelBits r.depth)
    let p := max (b+1) r.prec
    let r' := raiseWorkingPrecision r p
    Ready S (sourceDelta s) r' ∧ Stable s C r' ∧
      ¬ Nonempty (Fin (registerPrecision S r' (show Center S r' from t)+1) ↪ Probe S r') := by
  dsimp only
  let b := J9PrintedSchedule.degreeBound r.edges (2^(S).levelBits r.depth)
  let p := max (b+1) r.prec
  let r' := raiseWorkingPrecision r p
  refine ⟨raising_keeps_ready r p (Nat.le_max_right _ _) rd,
    raising_keeps_stable r p (Nat.le_max_right _ _) seed,?_⟩
  rintro ⟨emb⟩
  have given := Fintype.card_le_of_injective emb emb.injective
  rw [Fintype.card_fin,Fintype.card_fin] at given
  change registerPrecision S r' (show Center S r' from t)+1≤b+1 at given
  have grow : p≤registerPrecision S r' (show Center S r' from t) := by
    have hp : 0<r.edges := Nat.zero_lt_of_lt rd.active
    exact (child_monotone p ((S).levelBits r.depth) r.edges ((S).levelWidth r.depth) t.val hp).le
  have tooLarge : b+1≤p := Nat.le_max_left _ _
  omega

#print axioms packet_dominates_local_cost
#print axioms full_precision_fits_of_bounded_creation
#print axioms root_parameters_force_large_taper
#print axioms root_parameters_exact_packet_bits
#print axioms actual_odd_root_precision_formula
#print axioms actual_printed_root_full_precision_fits
#print axioms actual_printed_four_clone_full_precision_fits
#print axioms full_precision_selection_exists
#print axioms raising_keeps_stable
#print axioms raising_keeps_ready
#print axioms ready_stable_alone_does_not_supply_high_roster
end J8R64