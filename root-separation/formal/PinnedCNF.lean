import Std.Sat.CNF.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Pinned graph formulas, their induced-matching restrictions, and their zero test.
Edges have an arbitrary stored orientation. The literals and their evaluation use
the CNF syntax and semantics of Lean's standard library. -/

namespace PinnedCNF

open Finset
open scoped BigOperators

variable {V I : Type*}

/-- One unary clause per vertex and one positive binary clause per listed edge. -/
noncomputable def formula [Fintype V] (E : Finset (V × V)) (σ : V → Bool) :
    Std.Sat.CNF V :=
  (Finset.univ.toList.map fun v => [(v, σ v)]) ++
    (E.toList.map fun e => [(e.1, true), (e.2, true)])

def AllEdges (E : Finset (V × V)) (σ : V → Bool) : Prop :=
  ∀ e ∈ E, σ e.1 = true ∨ σ e.2 = true

theorem sat_iff [Fintype V] (E : Finset (V × V)) (σ x : V → Bool) :
    Std.Sat.CNF.Sat x (formula E σ) ↔ x = σ ∧ AllEdges E σ := by
  have hs : Std.Sat.CNF.Sat x (formula E σ) ↔ x = σ ∧ AllEdges E x := by
    simp [Std.Sat.CNF.sat_def, formula, Std.Sat.CNF.eval, List.all_eq_true,
      AllEdges, funext_iff]
  rw [hs]
  constructor <;> rintro ⟨rfl, h⟩ <;> exact ⟨rfl, h⟩

theorem satisfiable_iff [Fintype V] (E : Finset (V × V)) (σ : V → Bool) :
    (∃ x, Std.Sat.CNF.Sat x (formula E σ)) ↔ AllEdges E σ := by
  simp [sat_iff]

/-- Count every Boolean assignment accepted by the given CNF. -/
noncomputable def modelCount [Fintype V] (F : Std.Sat.CNF V) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : V → Bool => F.eval x = true).card

open scoped Classical in
theorem count_eq_indicator [Fintype V] (E : Finset (V × V)) (σ : V → Bool) :
    modelCount (formula E σ) = if AllEdges E σ then 1 else 0 := by
  classical
  have hf : (Finset.univ.filter fun x : V → Bool => (formula E σ).eval x = true) =
      (if AllEdges E σ then {σ} else ∅) := by
    ext x
    by_cases h : AllEdges E σ <;>
      simp [← Std.Sat.CNF.sat_def, sat_iff, h]
  unfold modelCount
  rw [hf]
  split_ifs <;> simp

/-- The two-bit OR table with entries in an arbitrary coefficient type. -/
def orEntry (R : Type*) [Zero R] [One R] : Matrix Bool Bool R :=
  Matrix.of fun x y => if x = true ∨ y = true then 1 else 0

theorem count_eq_edge_product [Fintype V] (E : Finset (V × V)) (σ : V → Bool) :
    modelCount (formula E σ) = ∏ e ∈ E, orEntry ℕ (σ e.1) (σ e.2) := by
  classical
  rw [count_eq_indicator]
  simp [orEntry, AllEdges, Finset.prod_boole]

theorem count_eq_sat_bit [Fintype V] (E : Finset (V × V)) (σ : V → Bool) :
    modelCount (formula E σ) =
      (open scoped Classical in if ∃ x, Std.Sat.CNF.Sat x (formula E σ) then 1 else 0) := by
  classical
  rw [count_eq_indicator]
  simp only [satisfiable_iff]

/-- Undirected adjacency of the stored edge list. -/
def Adj (E : Finset (V × V)) (u v : V) : Prop :=
  (u, v) ∈ E ∨ (v, u) ∈ E

/-- Give each edge of a graph on ordered vertices exactly one stored orientation. -/
noncomputable def edgesOf [Fintype V] [LinearOrder V] (G : V → V → Prop) :
    Finset (V × V) := by
  classical
  exact Finset.univ.filter fun e => e.1 < e.2 ∧ G e.1 e.2

theorem adj_edgesOf_iff [Fintype V] [LinearOrder V] (G : V → V → Prop)
    (hs : Symmetric G) (hi : Irreflexive G) (u v : V) :
    Adj (edgesOf G) u v ↔ G u v := by
  classical
  simp only [Adj, edgesOf, mem_filter, mem_univ, true_and]
  constructor
  · rintro (⟨_, huv⟩ | ⟨_, hvu⟩)
    · exact huv
    · exact hs hvu
  · intro huv
    rcases lt_trichotomy u v with h | rfl | h
    · exact Or.inl ⟨h, huv⟩
    · exact (hi _ huv).elim
    · exact Or.inr ⟨h, hs huv⟩

theorem allEdges_iff_adj (E : Finset (V × V)) (σ : V → Bool) :
    AllEdges E σ ↔ ∀ u v, Adj E u v → σ u = true ∨ σ v = true := by
  constructor
  · intro h u v huv
    rcases huv with huv | hvu
    · exact h _ huv
    · exact (h _ hvu).symm
  · intro h e he
    exact h e.1 e.2 (Or.inl he)

/-- Endpoints are distinct globally. The induced graph on them has exactly the
two-way adjacency between opposite endpoints with the same index. -/
structure InducedMatching (E : Finset (V × V)) (I : Type*) where
  endpoint : (I × Bool) ↪ V
  adj_iff : ∀ p q, Adj E (endpoint p) (endpoint q) ↔ p.1 = q.1 ∧ p.2 ≠ q.2

namespace InducedMatching

variable {E : Finset (V × V)} (M : InducedMatching E I)

/-- Assign the two transversals independently and assign true off the matching. -/
noncomputable def restrictSigns (x y : I → Bool) : V → Bool :=
  Function.extend M.endpoint (fun p => if p.2 then y p.1 else x p.1) (fun _ => true)

@[simp] theorem restrict_endpoint (x y : I → Bool) (p : I × Bool) :
    M.restrictSigns x y (M.endpoint p) = if p.2 then y p.1 else x p.1 :=
  M.endpoint.injective.extend_apply _ _ _

theorem restrict_outside (x y : I → Bool) {v : V} (h : ¬∃ p, M.endpoint p = v) :
    M.restrictSigns x y v = true :=
  Function.extend_apply' _ _ _ h

theorem allEdges_restrict_iff (x y : I → Bool) :
    AllEdges E (M.restrictSigns x y) ↔ ∀ i, x i = true ∨ y i = true := by
  rw [allEdges_iff_adj]
  constructor
  · intro h i
    have ha := h _ _ ((M.adj_iff (i, false) (i, true)).2 ⟨rfl, Bool.false_ne_true⟩)
    simpa only [restrict_endpoint, Bool.false_eq_true, ↓reduceIte] using ha
  · intro h u v huv
    by_cases hu : ∃ p, M.endpoint p = u
    · obtain ⟨⟨i, b⟩, rfl⟩ := hu
      by_cases hv : ∃ q, M.endpoint q = v
      · obtain ⟨⟨j, c⟩, rfl⟩ := hv
        obtain ⟨hij, hbc⟩ := (M.adj_iff _ _).1 huv
        change i = j at hij
        subst j
        cases b <;> cases c <;> simp_all [or_comm]
      · exact Or.inr (M.restrict_outside x y hv)
    · exact Or.inl (M.restrict_outside x y hu)

theorem restricted_count [Fintype V] [Fintype I] (x y : I → Bool) :
    modelCount (formula E (M.restrictSigns x y)) = ∏ i, orEntry ℕ (x i) (y i) := by
  classical
  rw [count_eq_indicator]
  simp only [allEdges_restrict_iff, orEntry, Matrix.of_apply, Fintype.prod_boole]

end InducedMatching

/-- Tensor power indexed directly by Boolean assignments to the coordinate set. -/
def tensorPower (I : Type*) [Fintype I] {R : Type*} [CommMonoid R]
    (A : Matrix Bool Bool R) : Matrix (I → Bool) (I → Bool) R :=
  Matrix.of fun x y => ∏ i, A (x i) (y i)

section Tensor

variable (I : Type*) [Fintype I] [DecidableEq I] {R : Type*} [CommRing R]

theorem tensorPower_mul (A B : Matrix Bool Bool R) :
    tensorPower I A * tensorPower I B = tensorPower I (A * B) := by
  ext x y
  change (∑ z : I → Bool, (∏ i, A (x i) (z i)) * (∏ i, B (z i) (y i))) =
    ∏ i, ∑ b : Bool, A (x i) b * B b (y i)
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i b => A (x i) b * B b (y i))).symm

omit [DecidableEq I] in
theorem tensorPower_one : tensorPower I (1 : Matrix Bool Bool R) = 1 := by
  ext x y
  change (∏ i, (1 : Matrix Bool Bool R) (x i) (y i)) =
    (1 : Matrix (I → Bool) (I → Bool) R) x y
  simp only [Matrix.one_apply, Fintype.prod_boole, funext_iff]

/-- Integer inverse of OR, interpreted in the given ring. -/
def orInv (R : Type*) [Ring R] : Matrix Bool Bool R
  | false, false => -1
  | false, true => 1
  | true, false => 1
  | true, true => 0

private theorem or_mul_inv : (orEntry R : Matrix Bool Bool R) * orInv R = 1 := by
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.mul_apply, Fintype.univ_bool, orEntry, orInv]

private theorem inv_mul_or : orInv R * (orEntry R : Matrix Bool Bool R) = 1 := by
  ext x y
  cases x <;> cases y <;>
    simp [Matrix.mul_apply, Fintype.univ_bool, orEntry, orInv]

theorem tensorOr_right_inverse :
    tensorPower I (orEntry R) * tensorPower I (orInv R) = 1 := by
  rw [tensorPower_mul, or_mul_inv, tensorPower_one]

theorem tensorOr_left_inverse :
    tensorPower I (orInv R) * tensorPower I (orEntry R) = 1 := by
  rw [tensorPower_mul, inv_mul_or, tensorPower_one]

theorem tensorOr_isUnit : IsUnit (tensorPower I (orEntry R)) :=
  ⟨⟨_, tensorPower I (orInv R), tensorOr_right_inverse I, tensorOr_left_inverse I⟩, rfl⟩

theorem tensorOr_rank [Nontrivial R] :
    (tensorPower I (orEntry R)).rank = 2 ^ Fintype.card I := by
  rw [Matrix.rank_of_isUnit _ (tensorOr_isUnit I), Fintype.card_fun, Fintype.card_bool]

end Tensor

namespace InducedMatching

variable {E : Finset (V × V)} (M : InducedMatching E I) [Fintype V] [Fintype I]

/-- Matrix of model counts of actual CNFs, embedded in the coefficient ring. -/
noncomputable def countMatrix (R : Type*) [AddMonoidWithOne R] :
    Matrix (I → Bool) (I → Bool) R :=
  Matrix.of fun x y => (modelCount (formula E (M.restrictSigns x y)) : R)

theorem countMatrix_eq_tensor (R : Type*) [CommRing R] :
    M.countMatrix R = tensorPower I (orEntry R) := by
  classical
  ext x y
  change (modelCount (formula E (M.restrictSigns x y)) : R) = ∏ i, orEntry R (x i) (y i)
  rw [count_eq_indicator, M.allEdges_restrict_iff]
  simp only [orEntry, Matrix.of_apply, Fintype.prod_boole]
  split_ifs <;> simp

theorem countMatrix_rank [DecidableEq I] (R : Type*) [CommRing R] [Nontrivial R] :
    (M.countMatrix R).rank = 2 ^ Fintype.card I := by
  rw [M.countMatrix_eq_tensor, tensorOr_rank]

theorem countMatrix_det_isUnit [DecidableEq I] (R : Type*) [CommRing R] :
    IsUnit (M.countMatrix R).det := by
  rw [M.countMatrix_eq_tensor, ← Matrix.isUnit_iff_isUnit_det]
  exact tensorOr_isUnit I

end InducedMatching

/-- The number of edge clauses falsified by the pin assignment. -/
def violations (E : Finset (V × V)) (σ : V → Bool) : ℕ :=
  ∑ e ∈ E, (1 - (σ e.1).toNat) * (1 - (σ e.2).toNat)

theorem violations_int (E : Finset (V × V)) (σ : V → Bool) :
    (violations E σ : ℤ) =
      ∑ e ∈ E, (1 - ((σ e.1).toNat : ℤ)) * (1 - ((σ e.2).toNat : ℤ)) := by
  simp only [violations, Nat.cast_sum, Nat.cast_mul, Nat.cast_sub (Bool.toNat_le _), Nat.cast_one]

private theorem edge_zero_iff (a b : Bool) :
    (1 - a.toNat) * (1 - b.toNat) = 0 ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

theorem violations_zero_iff (E : Finset (V × V)) (σ : V → Bool) :
    violations E σ = 0 ↔ AllEdges E σ := by
  unfold violations AllEdges
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [edge_zero_iff]

theorem count_by_zero_test [Fintype V] (E : Finset (V × V)) (σ : V → Bool) :
    modelCount (formula E σ) = if violations E σ = 0 then 1 else 0 := by
  classical
  rw [count_eq_indicator]
  simp only [violations_zero_iff]

theorem satisfiable_by_zero_test [Fintype V] (E : Finset (V × V)) (σ : V → Bool) :
    (∃ x, Std.Sat.CNF.Sat x (formula E σ)) ↔ violations E σ = 0 := by
  rw [satisfiable_iff, violations_zero_iff]

/-- One side's contribution at a vertex, as a function only of its restricted input. -/
noncomputable def sideWeight (P : V → Prop) (x : {v // P v} → Bool) (u : V) : ℕ := by
  classical
  exact if h : P u then 1 - (x ⟨u, h⟩).toNat else 1

noncomputable def sideFactor (P : V → Prop) (e : V × V) (x : {v // P v} → Bool) : ℕ :=
  sideWeight P x e.1 * sideWeight P x e.2

theorem violations_separated (E : Finset (V × V)) (σ : V → Bool) (P : V → Prop) :
    violations E σ = ∑ e ∈ E,
      sideFactor P e (fun v => σ v.1) * sideFactor (fun v => ¬P v) e (fun v => σ v.1) := by
  classical
  apply Finset.sum_congr rfl
  intro e _
  by_cases hu : P e.1 <;> by_cases hv : P e.2 <;>
    simp [sideFactor, sideWeight, hu, hv, Nat.mul_comm]

theorem count_eq_separated_zero_test [Fintype V] (E : Finset (V × V)) (σ : V → Bool)
    (P : V → Prop) :
    modelCount (formula E σ) = if (∑ e ∈ E,
      sideFactor P e (fun v => σ v.1) * sideFactor (fun v => ¬P v) e (fun v => σ v.1)) = 0
        then 1 else 0 := by
  rw [count_by_zero_test, violations_separated E σ P]

theorem violations_le_card (E : Finset (V × V)) (σ : V → Bool) :
    violations E σ ≤ E.card := by
  calc
    violations E σ ≤ ∑ _e ∈ E, 1 := by
      apply Finset.sum_le_sum
      intro e _
      cases σ e.1 <;> cases σ e.2 <;> decide
    _ = E.card := by simp

/-- The full-scope rational product for the exact count in Section 7. -/
theorem count_eq_rational_product [Fintype V] (E : Finset (V × V)) (σ : V → Bool) :
    (modelCount (formula E σ) : ℚ) =
      ∏ k ∈ Finset.Icc 1 E.card, (1 - (violations E σ : ℚ) / (k : ℚ)) := by
  by_cases h : violations E σ = 0
  · simp [count_by_zero_test, h]
  · rw [count_by_zero_test, if_neg h, Nat.cast_zero]
    symm
    apply Finset.prod_eq_zero (i := violations E σ)
    · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr h, violations_le_card E σ⟩
    · have hq : (violations E σ : ℚ) ≠ 0 := by exact_mod_cast h
      exact sub_eq_zero.mpr (div_self hq).symm

#print axioms sat_iff
#print axioms satisfiable_iff
#print axioms count_eq_indicator
#print axioms count_eq_edge_product
#print axioms count_eq_sat_bit
#print axioms adj_edgesOf_iff
#print axioms allEdges_iff_adj
#print axioms InducedMatching.restrict_endpoint
#print axioms InducedMatching.restrict_outside
#print axioms InducedMatching.allEdges_restrict_iff
#print axioms InducedMatching.restricted_count
#print axioms tensorPower_mul
#print axioms tensorPower_one
#print axioms tensorOr_right_inverse
#print axioms tensorOr_left_inverse
#print axioms tensorOr_isUnit
#print axioms tensorOr_rank
#print axioms InducedMatching.countMatrix_eq_tensor
#print axioms InducedMatching.countMatrix_rank
#print axioms InducedMatching.countMatrix_det_isUnit
#print axioms violations_int
#print axioms violations_zero_iff
#print axioms count_by_zero_test
#print axioms satisfiable_by_zero_test
#print axioms violations_separated
#print axioms count_eq_separated_zero_test
#print axioms violations_le_card
#print axioms count_eq_rational_product

end PinnedCNF
