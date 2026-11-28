import V8PooledMenuSlots

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

/-! Grading by the *sum* of the actual target exponents. This proof is
valid in the finite receiving ring, including zero divisors. No division
by a power of 2 is used. -/
namespace V8NativeMessage.N7
open scoped BigOperators Classical
variable {M R : Type*} [Fintype M] [CommRing R]

def modeCost (w : M→ℕ) (β : M→₀ℕ) : ℕ := ∑ m, w m*β m

@[simp] theorem modeCost_zero (w : M→ℕ) : modeCost w 0=0 := by
  simp [modeCost]

theorem modeCost_add (w : M→ℕ) (β γ : M→₀ℕ) :
    modeCost w (β+γ)=modeCost w β+modeCost w γ := by
  simp only [modeCost,Finsupp.add_apply,Nat.mul_add,Finset.sum_add_distrib]

theorem modeCost_single [DecidableEq M] (w : M→ℕ) (m : M) :
    modeCost w (Finsupp.single m 1)=w m := by
  unfold modeCost
  rw [Finset.sum_eq_single m]
  · simp
  · intro n _ hn
    simp [Ne.symm hn]
  · simp

def HasGain (w : M→ℕ) (q : MvPolynomial M R) : Prop :=
  ∀ β, (2:R)^modeCost w β ∣ q.coeff β

theorem gain_C (w : M→ℕ) (v : R) : HasGain w (MvPolynomial.C v) := by
  classical
  intro β
  by_cases hb : β=0
  · subst β
    simp
  · simpa only [MvPolynomial.coeff_C,if_neg (Ne.symm hb)] using
      (dvd_zero ((2:R)^modeCost w β))

theorem gain_single [DecidableEq M] (w : M→ℕ) (m : M) (v : R)
    (h : (2:R)^w m ∣ v) : HasGain w (MvPolynomial.monomial (Finsupp.single m 1) v) := by
  intro β
  rw [MvPolynomial.coeff_monomial]
  by_cases hβ : Finsupp.single m 1=β
  · subst β
    rwa [if_pos rfl,modeCost_single]
  · rw [if_neg hβ]
    exact dvd_zero _

theorem gain_add (w : M→ℕ) {q r : MvPolynomial M R} (hq : HasGain w q) (hr : HasGain w r) :
    HasGain w (q+r) := by
  intro β
  rw [MvPolynomial.coeff_add]
  exact dvd_add (hq β) (hr β)

theorem gain_sum {A : Type*} (s : Finset A) (f : A→MvPolynomial M R) (w : M→ℕ)
    (h : ∀ x∈s,HasGain w (f x)) : HasGain w (∑ x∈s, f x) := by
  intro β
  rw [MvPolynomial.coeff_sum]
  exact Finset.dvd_sum fun x hx => h x hx β

theorem gain_mul (w : M→ℕ) {q r : MvPolynomial M R} (hq : HasGain w q) (hr : HasGain w r) :
    HasGain w (q*r) := by
  classical
  intro β
  rw [MvPolynomial.coeff_mul]
  apply Finset.dvd_sum
  intro x hx
  rw [← Finset.mem_antidiagonal.mp hx,modeCost_add,pow_add]
  exact mul_dvd_mul (hq x.1) (hr x.2)

theorem gain_prod {A : Type*} (s : Finset A) (f : A→MvPolynomial M R) (w : M→ℕ)
    (h : ∀ x∈s,HasGain w (f x)) : HasGain w (∏ x∈s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty,← MvPolynomial.C_1]
    exact gain_C w 1
  | @insert a s hn ih =>
    rw [Finset.prod_insert hn]
    exact gain_mul w (h a (Finset.mem_insert_self _ _))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

theorem gain_row [DecidableEq M] (w : M→ℕ) (b : Bool) (val : R) (cross : M→R)
    (h : ∀ m,(2:R)^w m ∣ cross m) :
    HasGain w (J6RecursiveModes.row b val cross) := by
  unfold J6RecursiveModes.row
  apply gain_add w (gain_C _ _)
  apply gain_sum
  intro m _
  exact gain_single w m _ ((h m).trans (dvd_mul_left _ _))

theorem gain_packet {G K P : Type*} [DecidableEq G] [DecidableEq K] [DecidableEq M]
    (w : M→ℕ) (target source : M→G×K) (g : G) (k : K)
    (ports : Finset P) (bit : P→Bool) (base : P→R) (cross : P→M→R) (moment : M→R)
    (β : M→₀ℕ) (h : ∀ r∈ports,∀ m,(2:R)^w m ∣ cross r m) :
    (2:R)^modeCost w (β.filter (fun m=>target m=(g,k))) ∣
      J6RecursiveModes.packet target source g k ports bit base cross moment β := by
  unfold J6RecursiveModes.packet
  exact (gain_prod ports (fun r=>J6RecursiveModes.row (bit r) (base r) (cross r)) w
    (fun r hr=>gain_row w (bit r) (base r) (cross r) (h r hr)) _).trans (dvd_mul_right _ _)

theorem modeCost_partition {G K : Type*} [Fintype G] [Fintype K] [DecidableEq G] [DecidableEq K]
    (w : M→ℕ) (target : M→G×K) (β : M→₀ℕ) :
    ∑ g : G, ∑ k : K, modeCost w (β.filter (fun m=>target m=(g,k))) = modeCost w β := by
  classical
  let f (p : G×K) := modeCost w (β.filter (fun m=>target m=p))
  change (∑ g : G, ∑ k : K, f (g,k))=_
  rw [← Fintype.sum_prod_type f]
  simp only [f,modeCost,Finsupp.filter_apply,mul_ite,Nat.mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_eq_single (target m)]
  · simp
  · intro a _ ha
    simp [Ne.symm ha]
  · simp

#print axioms modeCost_add
#print axioms gain_mul
#print axioms gain_packet
#print axioms modeCost_partition
end V8NativeMessage.N7
