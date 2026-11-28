import GuardExpectation
import Mathlib.Data.Fintype.Card

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2100000

/-! The real primitive alphabet is conditioned coordinatewise.  A test
that reads at most four words is evaluated by a marginal sum over their
distinct primitive keys.  Unused keys are removed by normalization; keys
that coincide because of a vertex tie are used once, not made independent. -/
namespace J1R43Literal
open scoped BigOperators
open GuardExpectation

section Marginal
variable {P A : Type*} [DecidableEq P]

def cut (s : Finset P) : (P → A) ≃ (s → A) × ({p : P // p ∉ s} → A) where
  toFun z := ⟨fun a => z a.val, fun a => z a.val⟩
  invFun z p := if h : p ∈ s then z.1 ⟨p,h⟩ else z.2 ⟨p,h⟩
  left_inv z := by
    funext p
    by_cases hp : p ∈ s <;> simp [hp]
  right_inv z := by
    apply Prod.ext <;> funext p
    · simp [p.property]
    · simp [p.property]

variable [Fintype P] [Fintype A]

omit [Fintype A] in
theorem productMass_cut (s : Finset P) (w : P → A → ℚ) (z : P → A) :
    productMass w z =
      productMass (fun i : s => w i.val) (cut s z).1 *
      productMass (fun i : {p : P // p ∉ s} => w i.val) (cut s z).2 := by
  unfold productMass
  rw [← Equiv.prod_comp (Equiv.sumCompl (fun p => p ∈ s)) (fun j => w j (z j)),
      Fintype.prod_sum_type]
  rfl

theorem marginal (s : Finset P) (w : P → A → ℚ) (hw : ∀ i, ∑ a, w i a = 1)
    (f : (s → A) → ℚ) :
    average w (fun z => f (fun i => z i.val)) =
      average (fun i : s => w i.val) f := by
  let F := fun x : (s → A) × ({p : P // p ∉ s} → A) =>
    (productMass (fun i : s => w i.val) x.1 * f x.1) *
    productMass (fun i : {p : P // p ∉ s} => w i.val) x.2
  calc
    _ = ∑ z : P → A, F (cut s z) := by
      unfold average
      apply Finset.sum_congr rfl
      intro z _
      rw [productMass_cut s w z]
      unfold F
      change _ * _ * f ((cut s z).1) = _
      ring
    _ = ∑ x, F x := Equiv.sum_comp (cut s) F
    _ = _ := by
      rw [Fintype.sum_prod_type]
      unfold F
      have htail : (∑ y : ({p : P // p ∉ s} → A),
          productMass (fun i : {p : P // p ∉ s} => w i.val) y) = 1 :=
        sum_productMass (fun i : {p : P // p ∉ s} => w i.val) (fun i => hw i.val)
      simp only [← Finset.mul_sum, htail, mul_one]
      rfl

end Marginal

structure LocalTest (P A : Type*) where
  support : Finset P
  test : (support → A) → Bool

section Tests
variable {P A : Type*}

def LocalTest.value (x : LocalTest P A) (z : P → A) : ℚ :=
  if x.test (fun i => z i.val) then 1 else 0

def LocalTest.fromReads {T : Type*} [Fintype T] [DecidableEq P]
    (key : T → P) (f : (T → A) → Bool) : LocalTest P A where
  support := Finset.univ.image key
  test z := f (fun i => z ⟨key i,Finset.mem_image_of_mem key (Finset.mem_univ i)⟩)

theorem read_value {T : Type*} [Fintype T] [DecidableEq P]
    (key : T → P) (f : (T → A) → Bool) (z : P → A) :
    (LocalTest.fromReads key f).value z = if f (z ∘ key) then 1 else 0 := rfl

variable [Fintype P] [DecidableEq P] [Fintype A]

def LocalTest.conditional (x : LocalTest P A) (w : P → A → ℚ) : ℚ :=
  average (fun i : x.support => w i.val) (fun z => if x.test z then 1 else 0)

theorem local_conditional (x : LocalTest P A) (w : P → A → ℚ)
    (hw : ∀ i, ∑ a, w i a = 1) : average w x.value = x.conditional w := by
  exact marginal x.support w hw (fun z => if x.test z then 1 else 0)

variable {T I : Type*} [Fintype T] [Fintype I] [Nonempty A]

omit [Fintype P] in
theorem local_completions (key : T × I → P) (f : (T × I → A) → Bool)
    (hT : Fintype.card T ≤ 4) :
    Fintype.card (((LocalTest.fromReads key f).support) → A) ≤
      (Fintype.card A ^ Fintype.card I)^4 := by
  rw [Fintype.card_fun, Fintype.card_coe, ← pow_mul]
  apply Nat.pow_le_pow_right Fintype.card_pos
  change (Finset.univ.image key).card ≤ Fintype.card I * 4
  calc
    _ ≤ (Finset.univ : Finset (T × I)).card := Finset.card_image_le
    _ = Fintype.card T * Fintype.card I := by rw [Finset.card_univ,Fintype.card_prod]
    _ ≤ _ := by rw [Nat.mul_comm (Fintype.card I) 4]; exact Nat.mul_le_mul_right _ hT

end Tests

#print axioms productMass_cut
#print axioms marginal
#print axioms read_value
#print axioms local_conditional
#print axioms local_completions

end J1R43Literal