import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring

/-!
Literal truth-table compilation and exact completed-mode coefficient
extraction (v9 P3). A target is an actual port; one port can select at
most one mode. Exponent multiplicities do not label the selected copies.
The layout and crossing kernels remain inputs to this compiler.
-/

namespace LiteralPortCompiler

open scoped BigOperators
open MvPolynomial

section Literal

/-- The Boolean flag is true for a positive literal. -/
abbrev Lit (V : Type*) := V × Bool
abbrev CNF (V : Type*) := List (List (Lit V))

def lit {V : Type*} (a : V → Bool) (l : Lit V) : Bool :=
  if l.2 then a l.1 else !(a l.1)

def satisfied {V : Type*} (F : CNF V) (a : V → Bool) : Bool :=
  F.all fun c => c.any (lit a)

def indicator (R : Type*) [Zero R] [One R] (b : Bool) : R :=
  if b then 1 else 0

def truth {V R : Type*} [Zero R] [One R] (F : CNF V) (a : V → Bool) : R :=
  indicator R (satisfied F a)

def equality {V : Type*} (u v : V) : CNF V :=
  [[(u, false), (v, true)], [(u, true), (v, false)]]

def pin {V : Type*} (u : V) (s : Bool) : CNF V := [[(u, s)]]

theorem truth_equality {R V : Type*} [Zero R] [One R] (a : V → Bool) (u v : V) :
    (truth (equality u v) a : R) = if a u = a v then 1 else 0 := by
  cases hu : a u <;> cases hv : a v <;> simp [truth, equality, satisfied, lit, indicator, hu, hv]

theorem truth_pin {R V : Type*} [Zero R] [One R] (a : V → Bool) (u : V) (s : Bool) :
    (truth (pin u s) a : R) = if a u = s then 1 else 0 := by
  cases s <;> cases h : a u <;> simp [truth, pin, satisfied, lit, indicator, h]

theorem truth_append {R V : Type*} [MulZeroOneClass R] (A B : CNF V) (a : V → Bool) :
    (truth (A ++ B) a : R) = truth A a * truth B a := by
  unfold truth satisfied
  rw [List.all_append]
  cases (A.all fun c => c.any (lit a)) <;> cases (B.all fun c => c.any (lit a)) <;>
    simp [indicator]

end Literal

section Mode

noncomputable section

variable {P M R : Type*} [Fintype P] [DecidableEq M] [CommRing R]

/-- Baseline affine entry of a port, reading the actual Boolean label. -/
def affine (b : Bool) (x : R) : R := if b then x else 1-x

def slope (b : Bool) : R := if b then 1 else -1

def exponent (m : Option M) : M →₀ ℕ :=
  m.elim 0 (fun j => Finsupp.single j 1)

def modeWeight (scale : M → R) (β : M →₀ ℕ) : R := β.prod fun m e => scale m ^ e

theorem modeWeight_sum (scale : M → R) (a : P → Option M) :
    modeWeight scale (∑ p, exponent (a p)) = ∏ p, (a p).elim 1 scale := by
  classical
  have h (s : Finset P) :
      modeWeight scale (∑ p ∈ s, exponent (a p)) = ∏ p ∈ s, (a p).elim 1 scale := by
    induction s using Finset.induction_on with
    | empty => simp [modeWeight]
    | insert p s hp ih =>
      rw [Finset.sum_insert hp, Finset.prod_insert hp, ← ih]
      unfold modeWeight
      rw [Finsupp.prod_add_index (by intros; simp) (by intros; apply pow_add)]
      congr 1
      cases a p <;> simp [exponent, Finsupp.prod_single_index]
  exact h Finset.univ

variable [Fintype M] [DecidableEq P]

/-- Branch `none` uses the undeformed base entry; `some m` chooses the
single mode at that target port. A non-eligible port has kernel zero. -/
def portTerm (a : P → Bool) (base : (P → Bool) → P → R)
    (kernel : (P → Bool) → P → M → R) (p : P) (m : Option M) : R :=
  m.elim (affine (a p) (base a p)) (fun j => slope (a p) * kernel a p j)

def portPoly (a : P → Bool) (base : (P → Bool) → P → R)
    (kernel : (P → Bool) → P → M → R) (p : P) : MvPolynomial M R :=
  C (portTerm a base kernel p none) +
    ∑ m : M, monomial (Finsupp.single m 1) (portTerm a base kernel p (some m))

/-- Native completed polynomial before the coefficient projection: the sum
over the original Boolean port cube, using the unmodified literal table. -/
noncomputable def completed (F : CNF P) (base : (P → Bool) → P → R)
    (kernel : (P → Bool) → P → M → R) : MvPolynomial M R :=
  ∑ a : P → Bool, C (truth F a) * ∏ p, portPoly a base kernel p

omit [Fintype P] [Fintype M] [DecidableEq M] [DecidableEq P] in
theorem prod_monomials (s : Finset P) (a : P → Option M) (c : P → R) :
    (∏ p ∈ s, monomial (exponent (a p)) (c p)) =
      monomial (∑ p ∈ s, exponent (a p)) (∏ p ∈ s, c p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [monomial_zero']
  | insert p s hp ih =>
    rw [Finset.prod_insert hp, ih, monomial_mul, Finset.sum_insert hp, Finset.prod_insert hp]

/-- No multinomial coefficient is created by repeated modes. Every summand
is indexed once by its actual port-to-mode allocation. -/
theorem completed_coeff (F : CNF P) (base : (P → Bool) → P → R)
    (kernel : (P → Bool) → P → M → R) (β : M →₀ ℕ) :
    coeff β (completed F base kernel) =
      ∑ a : P → Bool, ∑ b : P → Option M,
        if (∑ p, exponent (b p)) = β
        then truth F a * ∏ p, portTerm a base kernel p (b p)
        else 0 := by
  classical
  have port (a : P → Bool) (p : P) :
      portPoly a base kernel p =
        ∑ m : Option M, monomial (exponent m) (portTerm a base kernel p m) := by
    simp [portPoly, Fintype.sum_option, exponent, monomial_zero']
  simp only [completed, port, Fintype.prod_sum, prod_monomials, Finset.mul_sum,
    C_mul_monomial, coeff_sum, coeff_monomial]

/-- Formal P3: the same homogeneous factor is extracted from every
allocation, including repeated modes, before any finite reduction. -/
theorem completed_normalized (F : CNF P) (base : (P → Bool) → P → R)
    (kernel : (P → Bool) → P → M → R) (scale : M → R) (β : M →₀ ℕ) :
    coeff β (completed F base (fun a p m => scale m * kernel a p m)) =
      modeWeight scale β * coeff β (completed F base kernel) := by
  classical
  have hp (a : P → Bool) (p : P) (b : Option M) :
      portTerm a base (fun a p m => scale m * kernel a p m) p b =
        b.elim 1 scale * portTerm a base kernel p b := by
    cases b <;> simp [portTerm, mul_left_comm]
  rw [completed_coeff, completed_coeff]
  simp only [Finset.mul_sum, hp, Finset.prod_mul_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : (∑ p, exponent (b p)) = β
  · rw [if_pos h, if_pos h, ← h, modeWeight_sum]
    ring
  · simp [h]

omit [Fintype P] [DecidableEq M] [DecidableEq P] in
/-- The polynomial is literally the affine extension of the original
port weight evaluated at the deformed baseline plus all crossing modes. -/
theorem portPoly_affine (a : P → Bool) (base : (P → Bool) → P → R)
    (kernel : (P → Bool) → P → M → R) (p : P) :
    portPoly a base kernel p = affine (a p)
      (C (base a p) + ∑ m : M, monomial (Finsupp.single m 1) (kernel a p m)) := by
  cases h : a p
  · have hneg (m : M) :
        monomial (Finsupp.single m 1) (-kernel a p m) =
          -(monomial (Finsupp.single m 1) (kernel a p m)) := map_neg _ _
    simp [portPoly, portTerm, affine, slope, h, hneg, Finset.sum_neg_distrib]
    ring
  · simp [portPoly, portTerm, affine, slope, h]

omit [Fintype P] [DecidableEq P] in
theorem map_truth {S : Type*} [CommRing S] (φ : R →+* S) (F : CNF P) (a : P → Bool) :
    φ (truth F a) = truth F a := by
  cases h : satisfied F a <;> simp [truth, indicator, h]

omit [Fintype P] [DecidableEq M] [Fintype M] [DecidableEq P] in
theorem map_portTerm {S : Type*} [CommRing S] (φ : R →+* S)
    (a : P → Bool) (base : (P → Bool) → P → R)
    (kernel : (P → Bool) → P → M → R) (p : P) (m : Option M) :
    φ (portTerm a base kernel p m) =
      portTerm a (fun x q => φ (base x q)) (fun x q j => φ (kernel x q j)) p m := by
  cases m <;> cases h : a p <;> simp [portTerm, affine, slope, h]

/-- Applying a ring homomorphism to each original entry before running the
finite compiler is equivalent to reducing the completed slot afterwards. -/
theorem reduce_completed {S : Type*} [CommRing S] (φ : R →+* S)
    (F : CNF P) (base : (P → Bool) → P → R)
    (kernel : (P → Bool) → P → M → R) (β : M →₀ ℕ) :
    φ (coeff β (completed F base kernel)) =
      coeff β (completed F (fun x q => φ (base x q))
        (fun x q j => φ (kernel x q j))) := by
  classical
  rw [completed_coeff, completed_coeff]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : (∑ p, exponent (b p)) = β
  · simp [h, map_mul, map_prod, map_truth, map_portTerm]
  · simp [h]

/-- The unique allocation attached to a chosen target port. -/
def atPort (p : P) (m : M) (q : P) : Option M := if q = p then some m else none

omit [DecidableEq M] [Fintype M] in
theorem atPort_exponent (p : P) (m : M) :
    (∑ q, exponent (atPort p m q)) = Finsupp.single m 1 := by
  classical
  rw [Finset.sum_eq_single_of_mem p (Finset.mem_univ p)]
  · simp [atPort, exponent]
  · intro q _ hq
    simp [atPort, exponent, hq]

omit [Fintype M] in
theorem singleton_unique (b : P → Option M) (m : M)
    (hb : (∑ p, exponent (b p)) = Finsupp.single m 1) :
    ∃! p, b = atPort p m := by
  classical
  have hpoint (j : M) :
      (∑ p, (exponent (b p)) j) = (Finsupp.single m 1) j := by
    rw [← Finsupp.finset_sum_apply, hb]
  have g (j : M) (p : P) : exponent (b p) j = if b p = some j then 1 else 0 := by
    cases b p with
    | none => simp [exponent]
    | some i => simp [exponent, Finsupp.single_apply]
  have hm (j : M) :
      (Finset.univ.filter (fun p => b p = some j)).card = if m = j then 1 else 0 := by
    simpa only [g, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finsupp.single_apply] using hpoint j
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp (by simpa using hm m)
  have hp0 : b p = some m := Finset.mem_filter.mp (show p ∈ Finset.univ.filter
      (fun q => b q = some m) by simp [hp]) |>.2
  have onlyM (q : P) (j : M) (hq : b q = some j) : m = j := by
    by_contra hn
    have hzero : (Finset.univ.filter (fun p => b p = some j)).card = 0 := (hm j).trans (if_neg hn)
    have hempty := Finset.card_eq_zero.mp hzero
    have hmem : q ∈ Finset.univ.filter (fun p => b p = some j) := by simp [hq]
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem
  have eb : b = atPort p m := by
    funext q
    by_cases hq : q = p
    · subst q
      simpa [atPort] using hp0
    · cases h : b q with
      | none => simp [atPort, hq]
      | some j =>
        obtain rfl := onlyM q j h
        have hmem : q ∈ Finset.univ.filter (fun q => b q = some m) := by simp [h]
        have hqp : q = p := by simpa [hp] using hmem
        exact False.elim (hq hqp)
  refine ⟨p, eb, ?_⟩
  intro q hq
  by_contra hn
  have hg := congrFun hq q
  have hzero := congrFun eb q
  simp [atPort, hn] at hg hzero
  simp_all

/-- The completed singleton is exactly the signed sum over one selected
original port, with every other port at its baseline. -/
theorem singleton_coeff (F : CNF P) (base : (P → Bool) → P → R)
    (kernel : (P → Bool) → P → M → R) (m : M) :
    coeff (Finsupp.single m 1) (completed F base kernel) =
      ∑ a : P → Bool, ∑ p : P,
        truth F a * ∏ q, portTerm a base kernel q (atPort p m q) := by
  classical
  rw [completed_coeff]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_filter]
  have himage : (Finset.univ.filter (fun b : P → Option M =>
      (∑ p, exponent (b p)) = Finsupp.single m 1)) =
      (Finset.univ : Finset P).image (fun p => atPort p m) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      obtain ⟨p, e, _⟩ := singleton_unique b m h
      exact ⟨p, e.symm⟩
    · rintro ⟨p, rfl⟩
      exact atPort_exponent p m
  rw [himage, Finset.sum_image]
  intro p _ q _ H
  by_contra h
  have ep := congrFun H p
  simp [atPort, h] at ep

end
end Mode

section Assembly

variable {G : Type*} [Fintype G] [DecidableEq G]
variable {P : G → Type*} [∀ g, Fintype (P g)] [∀ g, DecidableEq (P g)]
variable {S : Type*} [CommSemiring S]

/-- Precisely reindex the product of original child sums by the original
global Boolean cube. The kernels and mode coefficients may be interpreted
as fixed formal parameters at this step; no port assignment is identified
across different children. -/
theorem assemble_children (W : ∀ g, (P g → Bool) → S) :
    (∏ g, ∑ a : P g → Bool, W g a) =
      ∑ a : (Σ g, P g) → Bool, ∏ g, W g (fun p => a ⟨g,p⟩) := by
  classical
  rw [Fintype.prod_sum]
  let e : (∀ g, P g → Bool) ≃ ((Σ g, P g) → Bool) :=
    { toFun := fun a p => a p.1 p.2
      invFun := fun a g p => a ⟨g,p⟩
      left_inv := by intro a; rfl
      right_inv := by intro a; funext p; cases p; rfl }
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end Assembly

#print axioms truth_equality
#print axioms truth_pin
#print axioms truth_append
#print axioms modeWeight_sum
#print axioms portPoly_affine
#print axioms reduce_completed
#print axioms assemble_children
#print axioms completed_coeff
#print axioms completed_normalized
#print axioms singleton_unique
#print axioms singleton_coeff

end LiteralPortCompiler