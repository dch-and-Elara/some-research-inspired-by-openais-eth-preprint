import J6ActiveSchedule
import TruncatedProbeMenu

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

namespace V8PooledMenu
open scoped BigOperators Classical
open P1DyadicGrid J6ActiveSchedule

def shell (a i : ℕ) : Finset ℤ :=
  (grid a).filter (fun t => t≠0 ∧ padicValInt 2 t=i)

theorem mem_shell {a i : ℕ} {t : ℤ} :
    t∈shell a i ↔ t∈grid a ∧ t≠0 ∧ padicValInt 2 t=i := Finset.mem_filter

private theorem scaled_mesh {a i : ℕ} (hi : i≤a) (z : ℤ) :
    pow₂ i*z ∈ grid a ↔ z∈grid (a-i) := by
  have h := pow₂_pos i
  have he : pow₂ a = pow₂ i*pow₂ (a-i) := by
    rw [pow₂,pow₂,pow₂,← pow_add,Nat.add_sub_of_le hi]
  rw [mem_grid,mem_grid,he,← mul_neg,
    mul_le_mul_iff_right₀ h,mul_lt_mul_iff_right₀ h]

theorem shell_card_pow {a i : ℕ} (hi : i≤a) :
    (shell a i).card = 2^(a-i) := by
  let f : ℤ → ℤ := fun z => pow₂ i*z
  have hf : Function.Injective f := mul_right_injective₀ (ne_of_gt (pow₂_pos i))
  have he : (oddGrid (a-i)).image f = shell a i := by
    ext t
    simp only [Finset.mem_image,mem_shell,oddGrid,Finset.mem_filter]
    constructor
    · rintro ⟨z,⟨hz,ho⟩,rfl⟩
      exact ⟨(scaled_mesh hi z).mpr hz,
        mul_ne_zero (ne_of_gt (pow₂_pos i)) (odd_int_ne_zero ho),valuation_pow₂_mul_odd i ho⟩
    · rintro ⟨ht,ht0,htv⟩
      obtain ⟨z,hz,rfl⟩ := (level_iff_odd_multiplier ht0 i).mp htv
      exact ⟨z,⟨(scaled_mesh hi z).mp ht,hz⟩,rfl⟩
  rw [← he,Finset.card_image_of_injective _ hf,oddGrid_card]

theorem dyadic_div_pow {a i : ℕ} (hi : i≤a) :
    (2:ℕ)^a / 2^i = 2^(a-i) := by
  rw [← Nat.pow_sub_mul_pow (2:ℕ) hi]
  exact Nat.mul_div_cancel _ (by positivity)

theorem shell_card {a i : ℕ} (hi : i≤a) :
    (shell a i).card = 2^a / 2^i := by rw [shell_card_pow hi,dyadic_div_pow hi]

theorem active_iff {a M u : ℕ} (hu : 0<u) (huM : u≤M) {t : ℤ} :
    t∈active a M u ↔ t∈grid a ∧ t≠0 ∧ padicValInt 2 t<u := by
  have h : 0<height M u := by
    have hh := (height_bounds M u hu huM).1
    by_contra! h₀
    have he : height M u=0 := by omega
    rw [he,zero_mul] at hh
    omega
  simp only [active,Finset.mem_filter,Finset.mem_erase,order,Nat.mul_pos_iff_of_pos_left h, Nat.sub_pos_iff_lt]
  tauto

abbrev Center (a M u : ℕ) := ↥(active a M u)

def level {a M u : ℕ} (hu : 0<u) (huM : u≤M) (t : Center a M u) : Fin u :=
  ⟨padicValInt 2 t.val,((active_iff hu huM).mp t.property).2.2⟩

def centerChart {a M u : ℕ} (hu : 0<u) (huM : u≤M) :
    Center a M u ≃ (Σ i : Fin u, ↥(shell a i.val)) where
  toFun t := ⟨level hu huM t,
    ⟨t.val, (mem_shell).mpr
      ⟨((active_iff hu huM).mp t.property).1,((active_iff hu huM).mp t.property).2.1,rfl⟩⟩⟩
  invFun p := ⟨p.2.val, (active_iff hu huM).mpr
    ⟨(mem_shell.mp p.2.property).1,(mem_shell.mp p.2.property).2.1,
      ((mem_shell.mp p.2.property).2.2).symm ▸ p.1.isLt⟩⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨i,⟨t,ht⟩⟩
    have hi : (⟨padicValInt 2 t, ((mem_shell.mp ht).2.2).symm ▸ i.isLt⟩ : Fin u)=i :=
      Fin.ext ((mem_shell.mp ht).2.2)
    rcases i with ⟨j,hj⟩
    have hj' : padicValInt 2 t=j := (mem_shell.mp ht).2.2
    subst j
    rfl

def triangle (p : ℕ) : ℕ := p*(p+1)/2

def pooledBits (a u : ℕ) (prec : Fin u→ℕ) : ℕ :=
  ∑ i : Fin u, (2^a / 2^i.val) * triangle (prec i)

abbrev Tape {a M u : ℕ} (hu : 0<u) (huM : u≤M) (prec : Fin u→ℕ) :=
  (t : Center a M u) → TruncatedProbeMenu.NodeMessage (prec (level hu huM t))

theorem exact_tape_card {a M u : ℕ} (hu : 0<u) (huM : u≤M) (hua : u≤a)
    (prec : Fin u→ℕ) :
    Fintype.card (Tape (a:=a) hu huM prec) = 2^pooledBits a u prec := by
  classical
  rw [Fintype.card_pi]
  simp_rw [TruncatedProbeMenu.node_message_card]
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  change (∑ t : Center a M u, triangle (prec (level hu huM t))) = pooledBits a u prec
  unfold pooledBits
  have h := Fintype.sum_equiv (centerChart (a:=a) hu huM)
    (fun t => triangle (prec (level hu huM t))) (fun q => triangle (prec q.1)) (fun _ => rfl)
  rw [h,Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ _j : ↥(shell a i.val), triangle (prec i)) = _
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_coe,
    shell_card (i.isLt.le.trans hua)]
  simp

private theorem geometric_pow_sum (a u : ℕ) (h : u≤a) :
    (∑ i ∈ Finset.range u, (2:ℕ)^(a-i)) + 2^(a+1-u) = 2^(a+1) := by
  induction u with
  | zero => simp
  | succ u ih =>
    have hh := ih (by omega)
    have he : a+1-(u+1) = a-u := by omega
    have he' : a+1-u = (a-u)+1 := by omega
    rw [Finset.sum_range_succ, he, add_assoc, ← two_mul, ← pow_succ', ← he', hh]

theorem pooledBits_strict {a u : ℕ} (hua : u≤a)
    (prec : Fin u→ℕ) (hp : ∀ i, prec i ≤ a+1-i.val) :
    pooledBits a u prec < (2*2^a)*triangle (a+1) := by
  let C := triangle (a+1)
  have hC : 0<C := by
    unfold C triangle
    have hh : 2 ≤ (a+1)*(a+1+1) :=
      (by decide : 2≤1*2).trans (Nat.mul_le_mul (by omega) (by omega))
    omega
  have hpow (i : Fin u) : 2^a / 2^i.val = (2:ℕ)^(a-i.val) :=
    dyadic_div_pow (i.isLt.le.trans hua)
  have hsum : (∑ i : Fin u, (2:ℕ)^(a-i.val)) < 2^(a+1) := by
    rw [Fin.sum_univ_eq_sum_range (fun j => (2:ℕ)^(a-j)) u]
    have h := geometric_pow_sum a u hua
    have hzero : 0 < (2:ℕ)^(a+1-u) := by positivity
    omega
  have htri (i : Fin u) : triangle (prec i) ≤ C := by
    unfold C triangle
    exact Nat.div_le_div_right (Nat.mul_le_mul ((hp i).trans (Nat.sub_le _ _)) (by have := hp i; omega))
  calc
    pooledBits a u prec ≤ ∑ i : Fin u, (2:ℕ)^(a-i.val)*C := by
      unfold pooledBits
      exact Finset.sum_le_sum (fun i _ => by rw [hpow i]; exact Nat.mul_le_mul_left _ (htri i))
    _ = (∑ i : Fin u, (2:ℕ)^(a-i.val))*C := (Finset.sum_mul _ _ _).symm
    _ < (2*2^a)*triangle (a+1) := by
      rw [← pow_succ']
      exact Nat.mul_lt_mul_of_pos_right hsum hC

#print axioms shell_card
#print axioms active_iff
#print axioms centerChart
#print axioms exact_tape_card
#print axioms pooledBits_strict
end V8PooledMenu
