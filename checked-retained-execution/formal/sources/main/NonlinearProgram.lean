import Mathlib.Algebra.MvPolynomial.CommRing

/-! A native one-way scalar interface with shared nonlinear registers.
Every sender value has one variable, even when reused arbitrarily. Receiver
coefficients depend only on the receiver view. The semantics use actual DAG
registers, not an expansion into circuit paths. -/

namespace NonlinearProgram

variable {J X Y R : Type*}

inductive Gate (J Y R : Type*) (n : ℕ) where
  | source (j : J)
  | ambient (a : Y → R)
  | add (i j : Fin n)
  | mul (i j : Fin n)
  | neg (i : Fin n)

inductive Program (J Y R : Type*) : ℕ → Type _ where
  | empty : Program J Y R 0
  | push {n : ℕ} (prev : Program J Y R n) (gate : Gate J Y R n) :
      Program J Y R (n + 1)

variable [CommRing R]

def Gate.value {n : ℕ} (g : Gate J Y R n)
    (old : Fin n → X → Y → R) (message : J → X → R) : X → Y → R :=
  match g with
  | .source j => fun x _ => message j x
  | .ambient a => fun _ y => a y
  | .add i j => fun x y => old i x y + old j x y
  | .mul i j => fun x y => old i x y * old j x y
  | .neg i => fun x y => -(old i x y)

noncomputable def Gate.form {n : ℕ} (g : Gate J Y R n)
    (old : Fin n → Y → MvPolynomial J R) : Y → MvPolynomial J R :=
  match g with
  | .source j => fun _ => MvPolynomial.X j
  | .ambient a => fun y => MvPolynomial.C (a y)
  | .add i j => fun y => old i y + old j y
  | .mul i j => fun y => old i y * old j y
  | .neg i => fun y => -(old i y)

def Program.values (message : J → X → R) :
    {n : ℕ} → Program J Y R n → Fin n → X → Y → R
  | _, .empty => Fin.elim0
  | _, .push prev g => Fin.cases (g.value (prev.values message) message) (prev.values message)

noncomputable def Program.forms : {n : ℕ} → Program J Y R n → Fin n → Y → MvPolynomial J R
  | _, .empty => Fin.elim0
  | _, .push prev g => Fin.cases (g.form prev.forms) prev.forms

theorem Gate.form_eval {n : ℕ} (g : Gate J Y R n)
    (old : Fin n → Y → MvPolynomial J R) (message : J → X → R) (x : X) (y : Y) :
    MvPolynomial.eval (fun j => message j x) (g.form old y) =
      g.value (fun i x y => MvPolynomial.eval (fun j => message j x) (old i y))
        message x y := by
  cases g <;> simp [Gate.form, Gate.value]

theorem Program.polynomial_semantics {n : ℕ} (p : Program J Y R n)
    (message : J → X → R) (i : Fin n) (x : X) (y : Y) :
    MvPolynomial.eval (fun j => message j x) (p.forms i y) =
      p.values message i x y := by
  induction p generalizing x y with
  | empty => exact Fin.elim0 i
  | push prev g ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Program.forms, Program.values, Fin.cases_zero, Gate.form_eval]
      have h : (fun j x y => MvPolynomial.eval (fun k => message k x) (prev.forms j y)) =
          prev.values message := by
        funext j x' y'
        exact ih j x' y'
      rw [h]
    · exact ih j x y

/-- A concrete program always supplies a polynomial in the distinct messages;
no assumption bounds the degree or the number of expanded monomials. -/
theorem Program.exists_polynomial {n : ℕ} (p : Program J Y R n)
    (message : J → X → R) (i : Fin n) :
    ∃ P : Y → MvPolynomial J R,
      ∀ x y, p.values message i x y = MvPolynomial.eval (fun j => message j x) (P y) := by
  exact ⟨p.forms i, fun x y => (p.polynomial_semantics message i x y).symm⟩

section DualRail

/-- A positive two-rail implementation of AND. -/
def andRails (a na b nb : R) : R × R := (a * b, na + a * nb)

theorem andRails_true (a b : Bool) :
    (andRails (if a then 1 else 0 : R) (if a then 0 else 1 : R)
      (if b then 1 else 0 : R) (if b then 0 else 1 : R)).1 =
      if a && b then 1 else 0 := by
  cases a <;> cases b <;> simp [andRails]

theorem andRails_false (a b : Bool) :
    (andRails (if a then 1 else 0 : R) (if a then 0 else 1 : R)
      (if b then 1 else 0 : R) (if b then 0 else 1 : R)).2 =
      if a && b then 0 else 1 := by
  cases a <;> cases b <;> simp [andRails]

end DualRail

#print axioms Gate.form_eval
#print axioms Program.polynomial_semantics
#print axioms Program.exists_polynomial
#print axioms andRails_true
#print axioms andRails_false

end NonlinearProgram
