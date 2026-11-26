
import S11TaperLoss
import S11Interpolation
import S11Lift

noncomputable section
namespace S11

open Classical
open scoped BigOperators

abbrev Active (a u : ℕ) := centers u (2^a)

theorem active_mem_grid {u a : ℕ} (t : Active a u) : t.val ∈ grid (2^a) :=
  (Finset.mem_filter.1 t.property).1

theorem active_ne_zero {u a : ℕ} (t : Active a u) : t.val ≠ 0 :=
  (Finset.mem_filter.1 t.property).2.1

theorem active_level {u a : ℕ} (t : Active a u) : level t.val < u :=
  (Finset.mem_filter.1 t.property).2.2

def lossInt (M a u : ℕ) (t : Active a u) : ℤ :=
  ∑ q ∈ Finset.univ.erase t, (multiplicity M u q.val : ℤ) *
    ((level q.val : ℤ)-level (t.val-q.val))

theorem source_lossInt_lower (M a u : ℕ) (t : Active a u) :
    -6*(taper M u : ℤ)*(2 : ℤ)^(a-level t.val) ≤ lossInt M a u t := by
  have hl := tapered_cardinal_loss (active_mem_grid t) (active_ne_zero t) (taper M u) u
  let f (q : ℤ) := nonzeroWeight (taper M u) u q *
    ((level q:ℚ)-level (t.val-q))
  change _ ≤ ∑ q ∈ (grid (2^a)).erase t.val, f q at hl
  have hass :
      (∑ q ∈ Finset.univ.erase t, f q.val) = ∑ q ∈ (centers u (2^a)).erase t.val, f q := by
    apply Finset.sum_bij (fun q _ => q.val)
    · intro q hq
      exact Finset.mem_erase.2 ⟨fun he => (Finset.mem_erase.1 hq).1 (Subtype.ext he),q.property⟩
    · intro _ _ _ _ h
      exact Subtype.ext h
    · intro q hq
      obtain ⟨hn,hmem⟩ := Finset.mem_erase.1 hq
      exact ⟨⟨q,hmem⟩,Finset.mem_erase.2 ⟨fun he => hn (congrArg Subtype.val he),Finset.mem_univ _⟩,rfl⟩
    · intro _ _
      rfl
  have hsubset : (centers u (2^a)).erase t.val ⊆ (grid (2^a)).erase t.val := by
    intro q hq
    exact Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hq).1,
      (Finset.mem_filter.1 (Finset.mem_erase.1 hq).2).1⟩
  have he : (∑ q ∈ (centers u (2^a)).erase t.val, f q) =
      ∑ q ∈ (grid (2^a)).erase t.val, f q := by
    apply Finset.sum_subset hsubset
    intro q hq hn
    by_cases hq0 : q = 0
    · simp [f,nonzeroWeight,hq0]
    have hnu : u ≤ level q := by
      by_contra! hp
      exact hn (Finset.mem_erase.2 ⟨(Finset.mem_erase.1 hq).1,Finset.mem_filter.2
        ⟨(Finset.mem_erase.1 hq).2,hq0,hp⟩⟩)
    simp [f,nonzeroWeight,hq0,taperWeight,Nat.sub_eq_zero_of_le hnu]
  rw [← he, ← hass] at hl
  have hf (q : Active a u) : f q.val =
      (multiplicity M u q.val : ℚ) * ((level q.val:ℚ)-level (t.val-q.val)) := by
    simp [f,nonzeroWeight,active_ne_zero q,taperWeight,multiplicity]
  simp_rw [hf] at hl
  unfold lossInt
  exact_mod_cast hl

theorem source_taper_max {M u : ℕ} (hu : u ≤ M) (t : ℤ) :
    multiplicity M u t ≤ 4*M := by
  have hbound := Nat.div_mul_le_self (3*M+u-1) u
  change taper M u * u ≤ 3*M+u-1 at hbound
  exact (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans (hbound.trans (by omega))

private theorem Dpow {a i : ℕ} (hi : i ≤ a) : 2^a / 2^i = 2^(a-i) := by
  have he : a = (a-i)+i := by omega
  conv_lhs => lhs; rw [he,pow_add]
  exact Nat.mul_div_cancel _ (by positivity)

variable {K : Type*} [Field K] [CharZero K]

/-- The p_t published in D suffices for the origin coefficient of the
    native Hermite decoder. All losses are instantiated by the real
    active grid, its printed multiplicities, and its dyadic shift. -/
theorem source_taper_certified (v : AddValuation K (WithTop ℤ)) (h₂ : v (2:K) = 1)
    (M a u p : ℕ) (hM : 0 < M) (hu : 0 < u) (huM : u ≤ M) :
    S7.Certified v (fun t : Active a u => S7.scaledCenter a t.val)
      (fun t => multiplicity M u t.val)
      (fun t => precision p M a u (2^a) t.val) p 1 := by
  let x : Active a u → K := fun t => S7.scaledCenter a t.val
  let q : Active a u → ℕ := fun t => multiplicity M u t.val
  let gap : Active a u → ℕ := fun t => a+1-level t.val
  let c : Active a u → ℤ := lossInt M a u
  have hx : Function.Injective x := fun t s h =>
    Subtype.ext (S7.scaledCenter_injective v h₂ a h)
  have hq (t) : 0 < q t := by
    have ht := three_mul_le_taper_mul (M := M) hu
    have hl := active_level t
    have ht' : 0 < taper M u := by
      by_contra! hn
      have hz : taper M u = 0 := by omega
      rw [hz,zero_mul] at ht
      omega
    exact Nat.mul_pos ht' (by omega)
  have hval (t) : v (x t) = ↑(-(gap t:ℤ)) := by
    have h := S7.valuation_scaledCenter v h₂ a t.val (active_ne_zero t)
    have hl := level_grid (active_mem_grid t) (active_ne_zero t)
    change v (x t) = ↑((level t.val : ℤ) - ((a+1:ℕ):ℤ)) at h
    rw [h]
    congr 1
    dsimp [gap]
    rw [Nat.cast_sub (by omega),Nat.cast_add,Nat.cast_one]
    ring
  have hdiff (t s) (hn : t ≠ s) : 0 ≤ v ((x t-x s)⁻¹) := by
    have hn' : t.val ≠ s.val := fun h => hn (Subtype.ext h)
    dsimp [x]
    rw [S7.scaledCenter_diff,v.map_inv,S7.valuation_scaledCenter v h₂ _ _ (sub_ne_zero.2 hn'),
      ← WithTop.LinearOrderedAddCommGroup.coe_neg]
    have hl := level_diff_bound (active_mem_grid t) (active_mem_grid s) hn'
    exact_mod_cast (show (0:ℤ) ≤ -((level (t.val-s.val):ℤ)-((a+1:ℕ):ℤ)) by omega)
  have hc (t) : v ((S7.cardinal x q t).eval 0) = ↑(c t) :=
    S7.cardinal_valuation v h₂ a Subtype.val Subtype.val_injective active_ne_zero q t
  apply (S7.certified_iff_criterion v x hx q gap c _ p 1 hq (by decide) h₂ hval hc hdiff).2
  intro t
  have hi := level_grid (active_mem_grid t) (active_ne_zero t)
  have hD := Dpow hi
  have hL := source_lossInt_lower M a u t
  have hmargin := tapered_loss_fits p M a u (2^a) t.val
  rw [hD] at hmargin
  have hqb := source_taper_max (u:=u) huM t.val
  have hgb : gap t ≤ a+1 := Nat.sub_le _ _
  have hprod := Nat.mul_le_mul hqb hgb
  have hprod' : (q t : ℤ) * gap t ≤ 4 * M * (a+1) := by exact_mod_cast hprod
  have hnon : (0:ℤ) ≤ gap t := by positivity
  change ((1:ℤ)+q t-2)*(gap t) ≤ (precision p M a u (2^a) t.val:ℤ)-p+c t
  have hp' : (p:ℤ) + 6*(taper M u:ℤ)*(2:ℤ)^(a-level t.val) + 4*M*(a+1) ≤
      (precision p M a u (2^a) t.val:ℤ) := by exact_mod_cast hmargin
  unfold c
  nlinarith only [hL,hp',hprod',hnon]

#print axioms source_lossInt_lower
#print axioms source_taper_max
#print axioms source_taper_certified

end S11

