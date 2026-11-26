import S7ShellAverage
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Logic.Equiv.Fin.Basic

namespace S7
open Finset
open scoped BigOperators
noncomputable section

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The actual ordered centers of shell i in the full grid, where n = a-i. -/
def gridNode (i n : ℕ) (t : Shell n) : ℤ := 2^i*(2*(t.val:ℤ)+1-2^n)

theorem gridNode_bounds (i n : ℕ) (t : Shell n) :
    -(2:ℤ)^(i+n) ≤ gridNode i n t ∧ gridNode i n t < (2:ℤ)^(i+n) := by
  have ht : (t.val:ℤ) < (2:ℤ)^n := by exact_mod_cast t.isLt
  have h0 : 0 ≤ (t.val:ℤ) := by positivity
  rw [gridNode, pow_add]
  constructor
  · rw [← mul_neg]
    exact mul_le_mul_of_nonneg_left (by omega) (by positivity)
  · exact mul_lt_mul_of_pos_left (by omega) (by positivity)

theorem padicValInt_two_pow (i : ℕ) : padicValInt 2 ((2:ℤ)^i) = i := by
  rw [padicValInt, Int.natAbs_pow]
  exact padicValNat.prime_pow i

theorem gridNode_valuation (i n : ℕ) (hn : 0 < n) (t : Shell n) :
    padicValInt 2 (gridNode i n t) = i := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have hodd : ¬ (2:ℤ) ∣ 2*(t.val:ℤ)+1-2^k.succ := by
    simp only [pow_succ]
    omega
  have hnz : 2*(t.val:ℤ)+1-2^k.succ ≠ 0 := fun h => hodd (h ▸ dvd_zero _)
  rw [gridNode, padicValInt.mul (by positivity) hnz, padicValInt_two_pow,
    padicValInt.eq_zero_of_not_dvd hodd, add_zero]

theorem gridNode_injective (i n : ℕ) : Function.Injective (gridNode i n) := by
  intro t s h
  simp only [gridNode] at h
  have he := mul_left_cancel₀ (show (2:ℤ)^i ≠ 0 by positivity) h
  apply Fin.ext
  omega

theorem sameShell_distance (i n : ℕ) (t s : Shell n) (h : t ≠ s) :
    padicValInt 2 (gridNode i n t - gridNode i n s) =
      i + 1 + padicValInt 2 ((t.val:ℤ)-s.val) := by
  have he : gridNode i n t - gridNode i n s = (2:ℤ)^(i+1)*((t.val:ℤ)-s.val) := by
    simp only [gridNode, pow_succ]
    ring
  have hnz : (t.val:ℤ)-s.val ≠ 0 := by
    intro hh
    apply h
    apply Fin.ext
    omega
  rw [he, padicValInt.mul (by positivity) hnz, padicValInt_two_pow]

theorem residue_eq_iff_dvd {n : ℕ} (s : Fin n) (t x : Shell n) :
    residue s x = residue s t ↔ (2:ℤ)^s.val ∣ (x.val:ℤ) - t.val := by
  simp only [residue, Fin.mk.injEq]
  have h : (x.val : ℤ) % (2:ℤ)^s.val = (t.val : ℤ) % (2:ℤ)^s.val ↔
      (2:ℤ)^s.val ∣ (x.val:ℤ) - t.val := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.dvd_iff_emod_eq_zero]
  rw [← h]
  exact_mod_cast Iff.rfl

theorem differenceVal_lt {n : ℕ} (t x : Shell n) (h : x ≠ t) :
    padicValInt 2 ((x.val:ℤ)-t.val) < n := by
  by_contra! hp
  have hd := (padicValInt_dvd_iff (p:=2) n ((x.val:ℤ)-t.val)).2 (Or.inr hp)
  have hx : (x.val:ℤ) < (2:ℤ)^n := by exact_mod_cast x.isLt
  have ht : (t.val:ℤ) < (2:ℤ)^n := by exact_mod_cast t.isLt
  obtain ⟨z,hz⟩ := hd
  simp only [Nat.cast_ofNat] at hz
  have hpow : (0:ℤ) < 2^n := by positivity
  have hz0 : z = 0 := by
    by_contra h0
    rcases lt_or_gt_of_ne h0 with hh | hh
    · have hle : z ≤ -1 := by omega
      have hle' := mul_le_mul_of_nonneg_left hle hpow.le
      omega
    · have hge : 1 ≤ z := by omega
      have hge' := mul_le_mul_of_nonneg_left hge hpow.le
      omega
  apply h
  apply Fin.ext
  simp [hz0] at hz
  omega

theorem residue_threshold {n : ℕ} (i : ℕ) (s : Fin n) (t x : Shell n) (h : x ≠ t) :
    residue s x = residue s t ↔ i+(s.val+1) ≤
      padicValInt 2 (gridNode i n x - gridNode i n t) := by
  have hnz : (x.val:ℤ)-t.val ≠ 0 := by
    intro he
    apply h
    apply Fin.ext
    omega
  have hp := padicValInt_dvd_iff (p:=2) s.val ((x.val:ℤ)-t.val)
  simp only [Nat.cast_ofNat, hnz, false_or] at hp
  rw [residue_eq_iff_dvd, hp, sameShell_distance i n x t h]
  omega

/-- Every threshold class is a full arithmetic progression. -/
theorem residueClass_card {n : ℕ} (s : Fin n) (c : Fin (2^s.val)) :
    (univ.filter fun x : Shell n => residue s x = c).card = 2^(n-s.val) := by
  let e : Fin (2^(n-s.val)) × Fin (2^s.val) ≃ Shell n :=
    finProdFinEquiv.trans (finCongr (by rw [← pow_add]; congr 1; omega))
  have he (k : Fin (2^(n-s.val)) × Fin (2^s.val)) : residue s (e k) = k.2 := by
    apply Fin.ext
    change (k.2.val + 2^s.val * k.1.val) % 2^s.val = k.2.val
    rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt k.2.isLt]
  have hcard : (univ : Finset (Fin (2^(n-s.val)))).card = 2^(n-s.val) := by simp
  rw [← hcard]
  symm
  apply card_bij (fun k _ => e (k,c))
  · intro k _
    simp [he]
  · intro k _ l _ h
    exact congrArg Prod.fst (e.injective h)
  · intro x hx
    let k := e.symm x
    refine ⟨k.1,mem_univ _,?_⟩
    have hk : e k = x := e.apply_symm_apply x
    have hc := he k
    rw [hk, (mem_filter.mp hx).2] at hc
    rw [hc, Prod.eta, hk]

/-- P.7 for centers split by their valuations. The higher term is the sum
of (shell gap) times the mass in that shell. -/
theorem loss_split {A : Type*} [Fintype A] [DecidableEq A] (t : A)
    (q : A → ℚ) (level distance : A → ℕ)
    (hlo : ∀ s, level s < level t → distance s = level s)
    (hhi : ∀ s, level t < level s → distance s = level t) :
    (∑ s ∈ univ.erase t, q s*((distance s:ℚ)-level s)) =
      (∑ s ∈ (univ.erase t).filter (fun s => level s = level t),
        q s*((distance s:ℚ)-level t)) -
      (∑ s ∈ univ.filter (fun s => level t < level s), q s*((level s:ℚ)-level t)) := by
  have he : (univ.filter fun s => level t < level s) =
      (univ.erase t).filter (fun s => level t < level s) := by
    ext s
    simp only [mem_filter, mem_univ, true_and, mem_erase, and_true]
    constructor
    · exact fun h => ⟨fun hn => by subst s; omega, h⟩
    · exact And.right
  rw [he]
  simp only [sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro s _
  rcases lt_trichotomy (level s) (level t) with h|h|h
  · simp [hlo s h, h.ne, not_lt_of_ge h.le]
  · simp [h]
  · simp [hhi s h, Ne.symm h.ne, h]
    ring

theorem v2_neg (z : ℤ) : padicValInt 2 (-z) = padicValInt 2 z := by
  simp [padicValInt]

theorem gridNode_oddPart (n : ℕ) (hn : 0 < n) (t : Shell n) :
    ¬ (2:ℤ) ∣ 2*(t.val:ℤ)+1-2^n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  simp only [pow_succ]
  omega

theorem differentShell_distance (i j n m : ℕ) (hij : i < j) (hn : 0 < n)
    (t : Shell n) (s : Shell m) :
    padicValInt 2 (gridNode i n t - gridNode j m s) = i := by
  let f : ℤ := 2*(t.val:ℤ)+1-2^n
  let g : ℤ := 2*(s.val:ℤ)+1-2^m
  have he : gridNode i n t - gridNode j m s = (2:ℤ)^i*(f-2^(j-i)*g) := by
    have hp : (2:ℤ)^j = 2^i*2^(j-i) := by rw [← pow_add]; congr 1; omega
    rw [gridNode, gridNode, hp]
    dsimp [f,g]
    ring
  have hp : (2:ℤ) ∣ 2^(j-i)*g := by
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (show j-i ≠ 0 by omega)
    rw [hk, pow_succ]
    exact ⟨2^k*g, by ring⟩
  have hodd : ¬ (2:ℤ) ∣ f-2^(j-i)*g := by
    intro hd
    have hh := dvd_add hd hp
    rw [sub_add_cancel] at hh
    exact gridNode_oddPart n hn t hh
  have hne : f-2^(j-i)*g ≠ 0 := fun h => hodd (h ▸ dvd_zero _)
  rw [he, padicValInt.mul (by positivity) hne, padicValInt_two_pow,
    padicValInt.eq_zero_of_not_dvd hodd, add_zero]

/-- The shell parameterization is surjective onto the physical shell of the manuscript. -/
theorem gridNode_exists (i n : ℕ) (hn : 0 < n) {z : ℤ}
    (hlo : -(2:ℤ)^(i+n) ≤ z) (hhi : z < (2:ℤ)^(i+n))
    (hz : z ≠ 0) (hv : padicValInt 2 z = i) :
    ∃ t : Shell n, gridNode i n t = z := by
  have hd := padicValInt_dvd (p:=2) z
  rw [hv] at hd
  obtain ⟨y,hy⟩ := hd
  simp only [Nat.cast_ofNat] at hy
  have hyd : ¬ (2:ℤ) ∣ y := by
    intro h
    have hp : (2:ℤ)^(i+1) ∣ z := by
      obtain ⟨k,hk⟩ := h
      rw [hy,hk,pow_succ,← mul_assoc]
      exact dvd_mul_right _ _
    have hp' : (i+1) ≤ padicValInt 2 z := by
      have h := (padicValInt_dvd_iff (p:=2) (i+1) z).1 (by simpa only [Nat.cast_ofNat] using hp)
      exact h.resolve_left hz
    omega
  rw [hy, pow_add, ← mul_neg] at hlo
  rw [hy, pow_add] at hhi
  have pp : (0:ℤ) < 2^i := by positivity
  have hlow := le_of_mul_le_mul_left hlo pp
  have hhigh := lt_of_mul_lt_mul_left hhi pp.le
  have hdiv : (2:ℤ) ∣ (2:ℤ)^n := by
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    rw [pow_succ,mul_comm]
    exact dvd_mul_right _ _
  let x := (y+2^n-1)/2
  have hx : 0 ≤ x ∧ x < (2:ℤ)^n ∧ 2*x+1-2^n = y := by
    dsimp [x]
    omega
  let t : Shell n := ⟨x.toNat, by exact_mod_cast (show (x.toNat:ℤ) < (2:ℤ)^n by omega)⟩
  refine ⟨t,?_⟩
  rw [gridNode, hy]
  dsimp [t]
  rw [Int.toNat_of_nonneg hx.1, hx.2.2]

theorem shellInteraction_physical {n : ℕ} (i : ℕ) (q : Shell n → ℚ) (t : Shell n) :
    shellInteraction q t =
      ∑ s ∈ univ.erase t, q s*((padicValInt 2 (gridNode i n s-gridNode i n t):ℚ)-i) := by
  have hfilter : (univ : Finset (Shell n)).erase t = univ.filter (· ≠ t) := by
    ext s
    simp
  unfold shellInteraction
  simp only [hfilter, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro x _
  by_cases h : x = t
  · simp [h]
  have hx := differenceVal_lt t x h
  let r := padicValInt 2 ((x.val:ℤ)-t.val)+1
  have hr : r ≤ n := by dsimp [r]; omega
  have hthreshold (s : Fin n) : residue s x = residue s t ↔ s.val < r := by
    rw [residue_eq_iff_dvd]
    have hnz : (x.val:ℤ)-t.val ≠ 0 := by
      intro he
      apply h
      apply Fin.ext
      omega
    have hp := padicValInt_dvd_iff (p:=2) s.val ((x.val:ℤ)-t.val)
    simp only [Nat.cast_ofNat, hnz, false_or] at hp
    rw [hp]
    dsimp [r]
    omega
  simp [h, hthreshold]
  rw [Fin.sum_univ_eq_sum_range (fun s => if s < r then q x else 0), ← sum_filter]
  have he : (range n).filter (· < r) = range r := by
    ext s
    simp only [mem_filter, mem_range]
    omega
  rw [he, sum_const, card_range, nsmul_eq_mul, sameShell_distance i n x t h]
  dsimp [r]
  push_cast
  ring

/-- Sum of the distance valuation gaps for a constant-weight shell. -/
theorem uniform_interaction {n : ℕ} (Q : ℚ) (t : Shell n) :
    shellInteraction (fun _ => Q) t = Q*(2*((2:ℚ)^n-1)-n) := by
  have hf (s : Fin n) : (univ.filter fun x : Shell n => residue s x = residue s t ∧ x ≠ t) =
      (univ.filter fun x : Shell n => residue s x = residue s t).erase t := by
    ext x
    simp [and_comm]
  have hm (s : Fin n) : t ∈ univ.filter fun x : Shell n => residue s x = residue s t := by simp
  unfold shellInteraction
  simp only [hf, sum_const, card_erase_of_mem (hm _), residueClass_card, nsmul_eq_mul]
  have hC (s : Fin n) : (↑(2^(n-s.val)-1 : ℕ) : ℚ) = (2:ℚ)^n/2^s.val-1 := by
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by decide)), Nat.cast_pow]
    norm_num only [Nat.cast_ofNat, Nat.cast_one]
    have he : (2:ℚ)^n = 2^(n-s.val)*2^s.val := by rw [← pow_add]; congr 1; omega
    rw [he]
    field_simp
  simp_rw [hC, sub_mul, sum_sub_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun s => ((2:ℚ)^n/2^s)*Q)]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hh : (∑ s ∈ range n, ((2:ℚ)^n/2^s)*Q) = Q*2^n*(∑ s ∈ range n, (1:ℚ)/2^s) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro s _
    ring
  rw [hh, geometric]
  field_simp

end
end S7
