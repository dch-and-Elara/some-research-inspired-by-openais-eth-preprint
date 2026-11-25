import AffineCostRows

open scoped Polynomial BigOperators
open Polynomial

namespace AffineCost

/-- A rational arithmetic tree with only Boolean constants and label leaves. -/
inductive Expr (q : ℕ)
  | bit (b : Bool)
  | site (t : Fin q)
  | neg (x : Expr q)
  | inv (x : Expr q)
  | add (x y : Expr q)
  | mul (x y : Expr q)

namespace Expr

variable {q : ℕ} {F : Type*} [Field F]

def eval (a : Fin q → F) : Expr q → F
  | .bit b => if b then 1 else 0
  | .site t => a t
  | .neg x => -(eval a x)
  | .inv x => (eval a x)⁻¹
  | .add x y => eval a x + eval a y
  | .mul x y => eval a x * eval a y

def nodes : Expr q → ℕ
  | .bit _ | .site _ => 1
  | .neg x | .inv x => x.nodes+1
  | .add x y | .mul x y => x.nodes+y.nodes+1

theorem nodes_pos (x : Expr q) : 0 < x.nodes := by
  cases x <;> simp [nodes]

def sub (x y : Expr q) : Expr q := .add x (.neg y)

def sum : List (Expr q) → Expr q
  | [] => .bit false
  | x :: xs => .add x (sum xs)

theorem eval_sum (a : Fin q → F) (xs : List (Expr q)) :
    eval a (sum xs) = (xs.map (eval a)).sum := by
  induction xs <;> simp [sum, eval, *]

theorem sum_nodes (xs : List (Expr q)) (B : ℕ) (h : ∀ x ∈ xs, x.nodes ≤ B) :
    (sum xs).nodes ≤ 1+xs.length*(B+1) := by
  induction xs with
  | nil => simp [sum, nodes]
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht := ih fun y hy => h y (by simp [hy])
    simp only [sum,nodes,List.length_cons,Nat.add_mul,one_mul]
    omega

def negLabelProduct : List (Fin q) → Expr q
  | [] => .bit true
  | s :: ss => .mul (.neg (.site s)) (negLabelProduct ss)

theorem eval_negLabelProduct (a : Fin q → F) (l : List (Fin q)) :
    eval a (negLabelProduct l) = (l.map fun t => -a t).prod := by
  induction l <;> simp [negLabelProduct, eval, *]

theorem negLabelProduct_nodes (l : List (Fin q)) :
    (negLabelProduct l).nodes = 3*l.length+1 := by
  induction l with
  | nil => rfl
  | cons t l ih => simp [negLabelProduct, nodes, ih, Nat.mul_succ]; omega

/-- Compute a coefficient of the product of the linear factors. The tree
recursion deliberately avoids relying on polynomial arithmetic as a primitive. -/
def nodeCoeff : List (Fin q) → ℕ → Expr q
  | [], k => .bit (k == 0)
  | s :: ss, 0 => .mul (.neg (.site s)) (nodeCoeff ss 0)
  | s :: ss, k+1 => .add (nodeCoeff ss k) (.mul (.neg (.site s)) (nodeCoeff ss (k+1)))

theorem eval_nodeCoeff (a : Fin q → F) (l : List (Fin q)) (k : ℕ) :
    eval a (nodeCoeff l k) =
      ((l.map fun t => X - Polynomial.C (a t)).prod).coeff k := by
  induction l generalizing k with
  | nil =>
    cases k <;> simp [nodeCoeff, eval, Polynomial.coeff_one]
  | cons t l ih =>
    cases k with
    | zero =>
      simp [nodeCoeff, eval, ih, sub_mul, coeff_sub]
    | succ k =>
      simp only [nodeCoeff, eval, ih, List.map_cons, List.prod_cons, sub_mul,
        coeff_sub, coeff_X_mul, coeff_C_mul, neg_mul]
      ring

theorem nodeCoeff_nodes (l : List (Fin q)) (k : ℕ) :
    (nodeCoeff l k).nodes+4 ≤ 5*2^l.length := by
  induction l generalizing k with
  | nil => simp [nodeCoeff, nodes]
  | cons s ss ih =>
    cases k
    · have := ih 0
      simp only [nodeCoeff, nodes, List.length_cons, pow_succ]
      have he : 0 < 2^ss.length := Nat.pow_pos (by decide : 0 < (2:ℕ))
      omega
    · have := ih ‹ℕ›
      have := ih (‹ℕ›+1)
      simp only [nodeCoeff, nodes, List.length_cons, pow_succ]
      omega

end Expr
end AffineCost
