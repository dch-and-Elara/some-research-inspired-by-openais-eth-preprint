
import S11Kernel
import S7Valuation
import S7Arithmetic

noncomputable section
namespace S11

open scoped BigOperators
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def period (a : ℕ) : ℤ := (2 : ℤ)^(a+1)
def gridRep (a : ℕ) (z : ℤ) : ℤ := (z + (2:ℤ)^a) % period a - (2:ℤ)^a

theorem period_eq (a : ℕ) : period a = 2 * (2:ℤ)^a := by
  simp [period, pow_succ, mul_comm]

theorem grid_bounds {a : ℕ} {z : ℤ} :
    z ∈ grid (2^a) ↔ -(2:ℤ)^a ≤ z ∧ z < (2:ℤ)^a := by simp [grid]

theorem gridRep_mem (a : ℕ) (z : ℤ) : gridRep a z ∈ grid (2^a) := by
  rw [grid_bounds]
  have hp : 0 < period a := by unfold period; positivity
  have hlo := Int.emod_nonneg (z + 2^a) hp.ne'
  have hhi := Int.emod_lt_of_pos (z + 2^a) hp
  unfold gridRep
  rw [period_eq] at hlo hhi ⊢
  omega

theorem gridRep_congr (a : ℕ) (z : ℤ) : gridRep a z ≡ z [ZMOD period a] := by
  unfold gridRep
  simpa using (Int.mod_modEq (z + 2^a) (period a)).sub (Int.ModEq.refl ((2:ℤ)^a))

theorem gridRep_id {a : ℕ} {z : ℤ} (hz : z ∈ grid (2^a)) : gridRep a z = z := by
  rw [grid_bounds] at hz
  unfold gridRep
  rw [Int.emod_eq_of_lt (by omega) (by rw [period_eq]; omega)]
  omega

theorem grid_unique {a : ℕ} {x y : ℤ} (hx : x ∈ grid (2^a)) (hy : y ∈ grid (2^a))
    (h : x ≡ y [ZMOD period a]) : x = y := by
  have h' := h.add (Int.ModEq.refl ((2:ℤ)^a))
  have hrep : gridRep a x = gridRep a y := by
    unfold gridRep
    exact congrArg (fun z : ℤ => z - (2:ℤ)^a) h'
  simpa only [gridRep_id hx, gridRep_id hy] using hrep

def shiftGrid (a : ℕ) (t : ℤ) : (grid (2^a)) ≃ (grid (2^a)) where
  toFun q := ⟨gridRep a (t-q.val), gridRep_mem _ _⟩
  invFun q := ⟨gridRep a (t-q.val), gridRep_mem _ _⟩
  left_inv q := by
    apply Subtype.ext
    apply grid_unique (gridRep_mem _ _) q.property
    exact (gridRep_congr _ _).trans (by
      simpa using (Int.ModEq.refl t).sub (gridRep_congr a (t-q.val)))
  right_inv q := by
    apply Subtype.ext
    apply grid_unique (gridRep_mem _ _) q.property
    exact (gridRep_congr _ _).trans (by
      simpa using (Int.ModEq.refl t).sub (gridRep_congr a (t-q.val)))

theorem zero_mem_grid (a : ℕ) : (0 : ℤ) ∈ grid (2^a) := by
  rw [grid_bounds]
  have hp : (0 : ℤ) < 2^a := by positivity
  omega

theorem shiftGrid_center {a : ℕ} {t : ℤ} (ht : t ∈ grid (2^a)) :
    shiftGrid a t ⟨t,ht⟩ = ⟨0,zero_mem_grid a⟩ := by
  apply Subtype.ext
  change gridRep a (t-t) = 0
  rw [sub_self, gridRep_id (zero_mem_grid a)]

theorem level_bound {a : ℕ} {z : ℤ} (hz : z ≠ 0)
    (hlo : -period a < z) (hhi : z < period a) : level z ≤ a := by
  by_contra! h
  have hd := (padicValInt_dvd_iff (p := 2) (a+1) z).2 (Or.inr h)
  have hh := Int.natAbs_le_of_dvd_ne_zero hd hz
  have hh' : 2^(a+1) ≤ z.natAbs := by simpa only [Int.natAbs_pow, Int.natAbs_ofNat] using hh
  have he : ((2^(a+1):ℕ):ℤ) = period a := by simp [period]
  have hp : 0 < period a := by unfold period; positivity
  omega

theorem level_diff_bound {a : ℕ} {x y : ℤ} (hx : x ∈ grid (2^a)) (hy : y ∈ grid (2^a))
    (hne : x ≠ y) : level (x-y) ≤ a := by
  rw [grid_bounds] at hx hy
  apply level_bound (sub_ne_zero.2 hne) <;> rw [period_eq] <;> omega

theorem level_grid {a : ℕ} {x : ℤ} (hx : x ∈ grid (2^a)) (hne : x ≠ 0) :
    level x ≤ a := by
  simpa using level_diff_bound hx (zero_mem_grid a) hne

theorem same_level_of_congr {a : ℕ} {x y : ℤ} (hnx : x ≠ 0) (hny : y ≠ 0)
    (hx : level x ≤ a) (hy : level y ≤ a)
    (hxy : x ≡ y [ZMOD period a]) : level x = level y := by
  have hd {i : ℕ} (hi : i ≤ a+1) :
      ((2:ℤ)^i ∣ x) ↔ (2:ℤ)^i ∣ y := by
    have hper : (2:ℤ)^i ∣ period a := pow_dvd_pow _ hi
    have he : x % (2:ℤ)^i = y % (2:ℤ)^i := Int.modEq_iff_dvd.2
      (hper.trans (Int.modEq_iff_dvd.1 hxy))
    simp only [Int.dvd_iff_emod_eq_zero, he]
  apply le_antisymm
  · have h := padicValInt_dvd (p := 2) x
    exact ((padicValInt_dvd_iff (p := 2) (level x) y).1
      ((hd (by omega)).1 h)).resolve_left hny
  · have h := padicValInt_dvd (p := 2) y
    exact ((padicValInt_dvd_iff (p := 2) (level y) x).1
      ((hd (by omega)).2 h)).resolve_left hnx

theorem shiftGrid_level {a : ℕ} {t q : ℤ} (ht : t ∈ grid (2^a)) (hq : q ∈ grid (2^a))
    (hne : q ≠ t) : level (gridRep a (t-q)) = level (t-q) := by
  have h0 : gridRep a (t-q) ≠ 0 := by
    intro h
    have h1 : shiftGrid a t ⟨q,hq⟩ = shiftGrid a t ⟨t,ht⟩ := by
      rw [shiftGrid_center ht]
      exact Subtype.ext h
    exact hne (congrArg Subtype.val ((shiftGrid a t).injective h1))
  exact same_level_of_congr h0 (sub_ne_zero.2 hne.symm)
    (level_grid (gridRep_mem _ _) h0) (level_diff_bound ht hq hne.symm) (gridRep_congr _ _)

theorem valuation_multiset {a : ℕ} {t : ℤ} (ht : t ∈ grid (2^a))
    {A : Type*} [AddCommMonoid A] (f : ℕ → A) :
    (∑ q ∈ (grid (2^a)).erase t, f (level (t-q))) =
      ∑ q ∈ (grid (2^a)).erase 0, f (level q) := by
  classical
  let e := shiftGrid a t
  have hperm : (∑ q : grid (2^a), if q.val = t then 0 else f (level (t-q.val))) =
      ∑ q : grid (2^a), if q.val = 0 then 0 else f (level q.val) := by
    apply Fintype.sum_equiv e
    intro q
    by_cases h : q.val = t
    · have he : e q = ⟨0,zero_mem_grid a⟩ := by
        have hq : q = ⟨t,ht⟩ := Subtype.ext h
        rw [hq, shiftGrid_center ht]
      simp [h,he]
    · have he : (e q).val ≠ 0 := by
        intro hz
        apply h
        exact congrArg Subtype.val (e.injective ((Subtype.ext hz).trans (shiftGrid_center ht).symm))
      simp only [h, he, if_false]
      rw [show (e q).val = gridRep a (t-q.val) from rfl, shiftGrid_level ht q.property h]
  have hs (b : ℤ) (F : ℤ → A) :
      (∑ q : grid (2^a), if q.val = b then 0 else F q.val) =
      ∑ q ∈ (grid (2^a)).erase b, F q := by
    calc
      _ = ∑ q ∈ grid (2^a), if q = b then (0 : A) else F q :=
        Finset.sum_attach _ (fun q => if q = b then (0 : A) else F q)
      _ = _ := by
        rw [show (grid (2^a)).erase b = (grid (2^a)).filter (· ≠ b) by
          ext z; simp [and_comm], Finset.sum_filter]
        simp only [ite_not]
  exact (hs t (fun q => f (level (t-q)))).symm.trans (hperm.trans (hs 0 (fun q => f (level q))))

#print axioms shiftGrid_level
#print axioms valuation_multiset

end S11

