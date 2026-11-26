import J6R10RepackPhysical
import Mathlib.Data.Finset.Max
import J9PrintedSchedule

/-! Exact rounding from the printed collision statistic. We retain the
full cell load, round its actual maximum to the least multiple of L,
and discharge the padded budget under the source's numeric inequalities. -/
namespace J6R10Repack
open scoped Classical BigOperators
open P11FullPacking
variable {E C A B G : Type*}

abbrev Fiber (label : E → C) (c : C) := {e : E // label e = c}

noncomputable def maxFiber [Fintype C] (label : E → C) : ℕ :=
  Finset.univ.sup (fun c => Nat.card (Fiber label c))

theorem fiber_le_max [Fintype C] (label : E → C) (c : C) :
    Nat.card (Fiber label c) ≤ maxFiber label :=
  Finset.le_sup (f := fun k => Nat.card (Fiber label k)) (Finset.mem_univ c)

theorem attained_max [Fintype C] [Nonempty C] (label : E → C) :
    ∃ c : C, Nat.card (Fiber label c) = maxFiber label := by
  obtain ⟨c,_,hc⟩ := Finset.exists_max_image (Finset.univ : Finset C)
    (fun c => Nat.card (Fiber label c)) Finset.univ_nonempty
  exact ⟨c,le_antisymm (fiber_le_max label c) (Finset.sup_le hc)⟩

theorem printed_rounded_budget (M d L Δ maxLoad : ℕ) (hd : 0 < d) (hL : 0 < L)
    (hvariance : ((maxLoad:ℚ) - (M:ℚ)/d)^2 ≤ 2*(M:ℚ)*Δ)
    (hcollision : 2*d^2*Δ ≤ M) (hslots : L*d ≤ M) :
    d*(ceilCopies L maxLoad*L) ≤ 3*M := by
  have hdq : (0:ℚ)<d := by exact_mod_cast hd
  have hq : (2:ℚ)*(d:ℚ)^2*(Δ:ℚ) ≤ (M:ℚ) := by exact_mod_cast hcollision
  have hsquare : 2*(M:ℚ)*Δ ≤ ((M:ℚ)/d)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos hdq _)).mpr
    calc
      _ = (2*(d:ℚ)^2*(Δ:ℚ))*(M:ℚ) := by ring
      _ ≤ (M:ℚ)*(M:ℚ) := mul_le_mul_of_nonneg_right hq (by positivity)
      _ = _ := by ring
  have hupper : (maxLoad:ℚ) ≤ 2*((M:ℚ)/d) := by
    by_contra! h
    have hpos₁ : 0 < (maxLoad:ℚ)-2*((M:ℚ)/d) := sub_pos.mpr h
    have hpos₂ : (0:ℚ)<maxLoad := (by positivity : 0 ≤ 2*((M:ℚ)/d)).trans_lt h
    nlinarith [hvariance.trans hsquare,mul_pos hpos₁ hpos₂]
  have hload : maxLoad*d ≤ 2*M := by
    have hu : (maxLoad:ℚ) ≤ ((2:ℚ)*M)/d := by
      simpa only [mul_div_assoc] using hupper
    exact_mod_cast (le_div_iff₀ hdq).mp hu
  have hround := (rounded_capacity L maxLoad hL).2.le
  calc
    d*(ceilCopies L maxLoad*L) ≤ d*(maxLoad+L) := Nat.mul_le_mul_left _ hround
    _ = maxLoad*d + L*d := by ring
    _ ≤ 3*M := by omega

section Physical
variable [Fintype E] [LinearOrder G] [Fintype G] {a : ℕ}

noncomputable def varianceScore (label : E → Cell (Fin a) G) : ℚ :=
  ∑ c : Cell (Fin a) G,
    ((Nat.card (Fiber label c):ℚ) - (Nat.card E:ℚ)/Nat.card (Cell (Fin a) G))^2

/-- The printed variance witness, as opposed to a single-fibre bound,
gives a legal rounded packing with all labels still identical. -/
theorem actual_rounded_packing (N : Network E A B) (hG : Fintype.card G = 64)
    (rowLabel : A → Fin a → G) (colLabel : B → Fin a → G) (Δ : ℕ)
    (hvariance : varianceScore (declaredCell N rowLabel colLabel) ≤ 2*(Nat.card E:ℚ)*Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ ≤ Nat.card E)
    (hslots : 2^a * J9PrintedSchedule.arrayCard a ≤ Nat.card E) :
    ∃ P : PhysicalPacking N a G, P.rowLabel = rowLabel ∧ P.colLabel = colLabel ∧
      P.copies = ceilCopies (2^a) (maxFiber (declaredCell N rowLabel colLabel)) := by
  classical
  letI : Nonempty G := Fintype.card_pos_iff.mp (by omega)
  let label := declaredCell N rowLabel colLabel
  let d := Nat.card (Cell (Fin a) G)
  have hd : d = J9PrintedSchedule.arrayCard a := by
    unfold d J9PrintedSchedule.arrayCard
    rw [total_cells,hG]
  obtain ⟨c,hc⟩ := attained_max label
  have hv : ((maxFiber label:ℚ)-(Nat.card E:ℚ)/d)^2 ≤ 2*(Nat.card E:ℚ)*Δ := by
    rw [← hc]
    exact (Finset.single_le_sum (fun k _ => sq_nonneg
      ((Nat.card (Fiber label k):ℚ) - (Nat.card E:ℚ)/d)) (Finset.mem_univ c)).trans hvariance
  have hcap := printed_rounded_budget (Nat.card E) d (2^a) Δ (maxFiber label)
    (by rw [hd]; unfold J9PrintedSchedule.arrayCard; positivity) (by positivity)
    hv (hd ▸ hcollision) (hd ▸ hslots)
  exact ⟨rankedPacking N rowLabel colLabel (maxFiber label) (fiber_le_max label) hcap,rfl,rfl,rfl⟩
end Physical

#print axioms attained_max
#print axioms printed_rounded_budget
#print axioms actual_rounded_packing
end J6R10Repack
