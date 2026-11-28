import J3R59FractionFree
import J3R38LiteralSingletonTop
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000

/-! Substitute the real J3 matrix and the real native first-jet normalization
in the deterministic elimination. No left inverse, rank witness, pivot list,
row-value tape or solve is taken as an input; a catalogue just orders the
chosen menu and clone-family columns. -/
namespace J3R59
open scoped BigOperators

def rowDen {I : Type*} {n : ℕ}
    (A : I → Fin n → ℚ) (b : I → ℚ) (i : I) : ℕ :=
  (b i).den * ∏ j : Fin n, (A i j).den

def clearDen {I : Type*} (rows : List I) {n : ℕ}
    (A : I → Fin n → ℚ) (b : I → ℚ) : ℕ :=
  (rows.map (rowDen A b)).prod

theorem clearDen_nonzero {I : Type*} (rows : List I) {n : ℕ}
    (A : I → Fin n → ℚ) (b : I → ℚ) : clearDen rows A b ≠ 0 := by
  induction rows with
  | nil => exact one_ne_zero
  | cons i rs ih =>
    simp only [clearDen, List.map_cons, List.prod_cons] at *
    exact mul_ne_zero (mul_ne_zero (Rat.den_nz _) (Finset.prod_ne_zero_iff.mpr
      (fun j _ => Rat.den_nz (A i j)))) ih

theorem scaled_integer (d : ℕ) (q : ℚ) (h : q.den ∣ d) :
    ∃ z : ℤ, (d : ℚ) * q = z := by
  obtain ⟨k, rfl⟩ := h
  refine ⟨q.num * (k : ℤ), ?_⟩
  have hq : (q.den : ℚ) * q = q.num := by
    rw [mul_comm]
    exact ((div_eq_iff (Nat.cast_ne_zero.mpr (Rat.den_nz q))).mp
      (Rat.num_div_den q)).symm
  rw [Nat.cast_mul, Int.cast_mul, Int.cast_natCast, ← hq]
  ring

theorem cleared_entry_and_rhs_integral {I : Type*} (rows : List I) {n : ℕ}
    (A : I → Fin n → ℚ) (b : I → ℚ) (i : I) (hi : i ∈ rows) :
    (∀ j, ∃ z : ℤ, (clearDen rows A b : ℚ) * A i j = z) ∧
      ∃ z : ℤ, (clearDen rows A b : ℚ) * b i = z := by
  have hrow : rowDen A b i ∣ clearDen rows A b :=
    List.dvd_prod (List.mem_map_of_mem (f := rowDen A b) hi)
  constructor
  · intro j
    apply scaled_integer
    apply dvd_trans _ hrow
    exact dvd_trans (Finset.dvd_prod_of_mem (fun k : Fin n => (A i k).den)
      (Finset.mem_univ j)) (dvd_mul_left _ _)
  · exact scaled_integer _ _ (dvd_trans (dvd_mul_right _ _) hrow)

def solveScaled {I : Type*} (rows : List I) {n : ℕ}
    (A : I → Fin n → ℚ) (b : I → ℚ) : Option (Fin n → ℚ) :=
  let D : ℚ := (clearDen rows A b : ℚ)
  fractionFree rows n (fun i j => D * A i j) (fun i => D * b i) 1

theorem solveScaled_exact {I : Type*} (rows : List I) (allRows : ∀ i, i ∈ rows) {n : ℕ}
    (A : I → Fin n → ℚ) (b : I → ℚ)
    (inj : ∀ x : Fin n → ℚ, (∀ i, dot (A i) x = 0) → x = 0)
    (x : Fin n → ℚ) (hx : ∀ i, dot (A i) x = b i) :
    solveScaled rows A b = some x := by
  unfold solveScaled
  let D : ℚ := (clearDen rows A b : ℚ)
  have hD : D ≠ 0 := Nat.cast_ne_zero.mpr (clearDen_nonzero rows A b)
  have hdot (x' : Fin n → ℚ) (i : I) : dot (fun j => D * A i j) x' = D * dot (A i) x' := by
    simp only [dot, Finset.mul_sum, mul_assoc]
  apply fractionFree_exact rows allRows _ _ _ _ one_ne_zero
  · intro x' hz
    apply inj
    intro i
    have h := hz i
    rw [hdot] at h
    exact (mul_eq_zero.mp h).resolve_left hD
  · intro i
    rw [hdot, hx]

open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber
open J3R38LiteralSingleton
open scoped Classical
noncomputable section

variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J R : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v = 3}

def originalOrderedDecoder (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (A : Finset (Address W Q)) (rows : List {a // a ∈ A})
    (cols : Fin (Fintype.card W) ≃ W) (received : {a // a ∈ A} → Jet J) :
    Option (W → Bool) :=
  (solveScaled rows (fun a j => graphEntry hreg Prow a.val (cols j))
    (fun a => normalize P R hJ Prow a.val (received a))).map
    (fun x v => decide (x (cols.symm v) = 1))

/-- R40's literal full-column-rank graph test suffices for this specific
ordered algorithm, including integer clearing of the actual system. -/
theorem original_J3_fraction_free (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (hr : 2 ≤ r) (hR : 1 ≤ R) (hfit : 6*R ≤ Q)
    (A : Finset (Address W Q)) (ok : ∀ a ∈ A, Admissible hreg Prow a.1)
    (hRank : (graphMatrix hreg Prow A).rank = Fintype.card W)
    (rows : List {a // a ∈ A}) (allRows : ∀ a, a ∈ rows)
    (cols : Fin (Fintype.card W) ≃ W) (s : W → Bool) :
    originalOrderedDecoder (R := R) P Prow hJ A rows cols
      (fun a => rawJet P R hJ Prow a.val s) = some s := by
  let G (a : {a // a ∈ A}) (v : W) : ℚ := graphEntry hreg Prow a.val v
  let M := graphMatrix hreg Prow A
  have hdim : M.rank + Module.finrank ℚ (LinearMap.ker M.mulVecLin) = Fintype.card W := by
    simpa only [Matrix.rank, Module.finrank_pi] using
      (LinearMap.finrank_range_add_finrank_ker M.mulVecLin)
  have hm : M.rank = Fintype.card W := hRank
  have hk : LinearMap.ker M.mulVecLin = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    omega
  have reindex (a : {a // a ∈ A}) (z : W → ℚ) :
      dot (fun j => G a (cols j)) (fun j => z (cols j)) = ∑ v, G a v * z v := by
    apply Fintype.sum_equiv cols
    exact fun _ => rfl
  have inj (x : Fin (Fintype.card W) → ℚ)
      (hx : ∀ a, dot (fun j => G a (cols j)) x = 0) : x = 0 := by
    let y : W → ℚ := fun v => x (cols.symm v)
    have hz : M.mulVecLin y = 0 := by
      funext a
      change (∑ v, G a v * y v) = 0
      have he := reindex a y
      have hy : (fun j => y (cols j)) = x := by
        funext j
        simp [y]
      rw [hy, hx] at he
      exact he.symm
    have hy := (LinearMap.ker_eq_bot.mp hk) (show M.mulVecLin y = M.mulVecLin 0 by
      rw [map_zero]
      exact hz)
    funext j
    have hj := congrFun hy (cols j)
    simpa [y] using hj
  let z (v : W) : ℚ := JointContraction.bitScalar ℚ (s v)
  have hsol (a : {a // a ∈ A}) :
      dot (fun j => G a (cols j)) (fun j => z (cols j)) =
        normalize P R hJ Prow a.val (rawJet P R hJ Prow a.val s) :=
    (reindex a z).trans (original_J3_equation P Prow hJ hr hR hfit a.val (ok _ a.property) s).2.symm
  unfold originalOrderedDecoder
  rw [solveScaled_exact rows allRows (fun a j => G a (cols j)) _ inj _ hsol]
  simp only [Option.map_some]
  congr 1
  funext v
  simp only [cols.apply_symm_apply]
  cases hs : s v <;> simp [z, JointContraction.bitScalar, hs]

#print axioms clearDen_nonzero
#print axioms cleared_entry_and_rhs_integral
#print axioms solveScaled_exact
#print axioms original_J3_fraction_free

end
end J3R59
