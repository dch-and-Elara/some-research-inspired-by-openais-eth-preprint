import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! Exact weighted collision energy for arbitrary many finite partitions.
This is the finite combinatorial identity/Cauchy step in (P.8). The
raw signed-grid realization of these partitions is a separate lemma. -/
namespace Paper5.PrecisionOpt
open scoped BigOperators

variable {T C J : Type*} [Fintype T] [Fintype C] [DecidableEq C]

def classMass (ρ : T→C) (w : T→ℚ) (c : C) : ℚ :=
  ∑ t∈Finset.univ.filter (fun t => ρ t=c),w t

theorem classMass_sum (ρ : T→C) (w : T→ℚ) : (∑ c,classMass ρ w c)=∑ t,w t :=
  Finset.sum_fiberwise Finset.univ ρ w

theorem classEnergy (ρ : T→C) (w : T→ℚ) :
    (∑ t,∑ s,if ρ t=ρ s then w t*w s else 0) = ∑ c,classMass ρ w c^2 := by
  classical
  have h1 (t : T) : (∑ s,if ρ t=ρ s then w t*w s else 0) = w t*classMass ρ w (ρ t) := by
    unfold classMass
    rw [Finset.mul_sum,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s _
    by_cases h : ρ t=ρ s
    · rw [if_pos h.symm,if_pos h]
    · rw [if_neg (Ne.symm h),if_neg h]
  simp only [h1]
  rw [←Finset.sum_fiberwise Finset.univ ρ (fun t => w t*classMass ρ w (ρ t))]
  apply Finset.sum_congr rfl
  intro c _
  have he : (∑ s∈Finset.univ.filter (fun s => ρ s=c),w s*classMass ρ w (ρ s)) =
      ∑ s∈Finset.univ.filter (fun s => ρ s=c),w s*classMass ρ w c := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [(Finset.mem_filter.mp hs).2]
  rw [he,←Finset.sum_mul]
  change classMass ρ w c*classMass ρ w c = _
  rw [pow_two]

theorem classEnergy_bound (ρ : T→C) (w : T→ℚ) (hC : 0<Fintype.card C) :
    (∑ t,w t)^2/(Fintype.card C:ℚ) ≤ ∑ c,classMass ρ w c^2 := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset C)
    (classMass ρ w) (fun _ => (1:ℚ))
  simp only [mul_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,classMass_sum] at hc
  have hn : 0<(Fintype.card C:ℚ) := by exact_mod_cast hC
  exact (div_le_iff₀ hn).mpr hc

variable [DecidableEq T]

def offEnergy (ρ : T→C) (w : T→ℚ) : ℚ :=
  ∑ t,∑ s∈Finset.univ.erase t,if ρ t=ρ s then w t*w s else 0

theorem classEnergy_remove_diagonal (ρ : T→C) (w : T→ℚ) :
    offEnergy ρ w+(∑ t,w t^2) = ∑ c,classMass ρ w c^2 := by
  rw [←classEnergy]
  unfold offEnergy
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  have hh := Finset.sum_erase_add (Finset.univ : Finset T)
    (fun s => if ρ t=ρ s then w t*w s else 0) (Finset.mem_univ t)
  simpa only [if_true,pow_two] using hh

omit [Fintype C] [DecidableEq C] in
theorem weighted_threshold_energy [Fintype J] (D : T→T→ℕ) (w : T→ℚ) (m : J→ℕ)
    (ρ : ∀ j : J,T→Fin (m j))
    (hD : ∀ t s, s≠t → D t s = ∑ j,if ρ j t=ρ j s then (1:ℕ) else 0) :
    (∑ t,∑ s∈Finset.univ.erase t,w t*w s*(D t s:ℚ)) +
       (Fintype.card J:ℚ)*(∑ t,w t^2) =
      ∑ j,∑ c,classMass (ρ j) w c^2 := by
  have hrow (t : T) :
      (∑ s∈Finset.univ.erase t,w t*w s*(D t s:ℚ)) =
        ∑ j,∑ s∈Finset.univ.erase t,if ρ j t=ρ j s then w t*w s else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s hs
    rw [hD t s (Finset.ne_of_mem_erase hs),Nat.cast_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    by_cases he : ρ j t=ρ j s <;> simp [he]
  simp_rw [hrow]
  rw [Finset.sum_comm]
  have hcard : (Fintype.card J:ℚ)*(∑ t,w t^2) = ∑ _j : J,∑ t,w t^2 := by simp
  rw [hcard,←Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => classEnergy_remove_diagonal (ρ j) w)

omit [Fintype C] [DecidableEq C] in
theorem arbitrary_weight_p8 [Fintype J] (D : T→T→ℕ) (w : T→ℚ) (m : J→ℕ)
    (ρ : ∀ j : J,T→Fin (m j)) (hm : ∀ j,0<m j)
    (hD : ∀ t s,s≠t → D t s = ∑ j,if ρ j t=ρ j s then (1:ℕ) else 0) :
    (∑ j,(∑ t,w t)^2/(m j:ℚ)) ≤
      (∑ t,∑ s∈Finset.univ.erase t,w t*w s*(D t s:ℚ))+
       (Fintype.card J:ℚ)*(∑ t,w t^2) := by
  rw [weighted_threshold_energy D w m ρ hD]
  apply Finset.sum_le_sum
  intro j _
  have hC : 0<Fintype.card (Fin (m j)) := by simpa using hm j
  simpa only [Fintype.card_fin] using classEnergy_bound (ρ j) w hC

theorem dyadic_reciprocal_sum (n : ℕ) :
    (∑ j∈Finset.range n,(1:ℚ)/2^j)=2*(1-(1:ℚ)/2^n) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,pow_succ]
    field_simp
    ring

#print axioms classEnergy
#print axioms classEnergy_bound
#print axioms classEnergy_remove_diagonal
#print axioms weighted_threshold_energy
#print axioms arbitrary_weight_p8
#print axioms dyadic_reciprocal_sum
end Paper5.PrecisionOpt
