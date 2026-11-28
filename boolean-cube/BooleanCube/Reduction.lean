import BooleanCube.Invariant
import Mathlib.Algebra.Polynomial.BigOperators

namespace LocalReconstruction
open Polynomial
open scoped Polynomial

noncomputable section

def flip {q : ℕ} (i : Fin q) (s : Cube q) : Cube q := toggle s (oneBit i)

def flipEquiv {q : ℕ} (i : Fin q) : Cube q ≃ Cube q where
  toFun := flip i
  invFun := flip i
  left_inv s := by funext j; simp [flip, toggle]
  right_inv s := by funext j; simp [flip, toggle]

theorem walsh_flip {q : ℕ} (i : Fin q) (s x : Cube q) :
    walsh (flip i s) x = walsh s x * signBit true (x i) := by
  have hs : walsh (oneBit i) x = signBit true (x i) := by
    unfold walsh
    calc
      _ = ∏ j, (if j = i then signBit true (x j) else 1) := by
        apply Finset.prod_congr rfl
        intro j _
        by_cases h : j = i
        · simp [oneBit, h]
        · simp [oneBit, h, signBit]
      _ = _ := Fintype.prod_ite_eq' _ _
  rw [walsh_comm (flip i s), flip, walsh_toggle, walsh_comm x s, walsh_comm x (oneBit i), hs]

def edgeCondition {q : ℕ} (labels : Fin q → ℚ) (A : Set (Cube q)) (d : ℕ)
    (p : Cube q → ℚ[X]) : Prop :=
  (∀ s, (p s).natDegree ≤ d) ∧ (∀ s, (p s).eval 0 = 1) ∧
  ∀ i s, s ∉ A → flip i s ∉ A → (p s).eval (labels i) + (p (flip i s)).eval (labels i) = 0

def rowSpace {ι : Type*} {q : ℕ} (C : Matrix ι (Cube q) ℚ) : Submodule ℚ (Cube q → ℚ) :=
  Submodule.span ℚ (Set.range C)

def rowTest {ι : Type*} {q : ℕ} (C : Matrix ι (Cube q) ℚ) (h : Cube q → ℚ) : Prop :=
  ∀ j, ∑ x, C j x * h x = 0

def halfSupport {q : ℕ} (i : Fin q) (u : Cube q) (h : Cube q → ℚ) : Prop :=
  ∀ x, x i ≠ u i → h x = 0

def matrixCondition {ι : Type*} {q : ℕ} (labels : Fin q → ℚ) (C : Matrix ι (Cube q) ℚ)
    (d : ℕ) (P : Matrix (Cube q) (Cube q) ℚ[X]) : Prop :=
  (∀ u v, (P u v).natDegree ≤ d) ∧
  (∀ u v, (P u v).eval 0 = if u = v then 1 else 0) ∧
  ∀ u i h, rowTest C h → halfSupport i u h → ∑ v, (P u v).eval (labels i) * h v = 0

private def pairing {q : ℕ} (h : Cube q → ℚ) : (Cube q → ℚ) →ₗ[ℚ] ℚ where
  toFun f := ∑ x, h x * f x
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' a f := by simp [Finset.mul_sum, mul_left_comm]

theorem kernel_walsh {ι : Type*} {q : ℕ} {C : Matrix ι (Cube q) ℚ} {A : Set (Cube q)}
    (hW : rowSpace C = walshSpace A) (h : Cube q → ℚ) :
    rowTest C h ↔ ∀ s ∈ A, coefficient s h = 0 := by
  have lhs : rowTest C h ↔ rowSpace C ≤ (pairing h).ker := by
    rw [rowSpace, Submodule.span_le]
    constructor
    · rintro hc _ ⟨j,rfl⟩
      simpa [LinearMap.mem_ker, pairing, mul_comm] using hc j
    · intro hc j
      have hmem := hc (Set.mem_range_self j)
      simpa [LinearMap.mem_ker, pairing, mul_comm] using hmem
  rw [lhs, hW, walshSpace, Submodule.span_le]
  constructor
  · intro hmem s hs
    exact hmem ⟨s,hs,rfl⟩
  · rintro hmem _ ⟨s,hs,rfl⟩
    exact hmem s hs

private theorem coefficient_pair {q : ℕ} (a b z : Cube q) :
    coefficient z (walsh a + walsh b) =
      (if a = z then (2:ℚ)^q else 0) + (if b = z then (2:ℚ)^q else 0) := by
  simp [coefficient, add_mul, Finset.sum_add_distrib, walsh_orthogonal]

theorem matrix_to_edges {ι : Type*} {q d : ℕ} {labels : Fin q → ℚ}
    {C : Matrix ι (Cube q) ℚ} {A : Set (Cube q)} (hW : rowSpace C = walshSpace A)
    {P : Matrix (Cube q) (Cube q) ℚ[X]} (hp : matrixCondition labels C d P) :
    ∃ p, edgeCondition labels A d p := by
  classical
  let o : Cube q := fun _ => false
  let p := fun s : Cube q => ∑ v : Cube q, Polynomial.C (walsh s v) * P o v
  obtain ⟨hdeg,hzero,hact⟩ := hp
  refine ⟨p, ?_, ?_, ?_⟩
  · intro s
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro v _
    exact (natDegree_C_mul_le _ _).trans (hdeg o v)
  · intro s
    have ho : walsh s o = 1 := by
      unfold walsh
      apply Finset.prod_eq_one
      intro i _
      cases s i <;> rfl
    simp [p, eval_finset_sum, hzero, mul_ite, ho]
  · intro i s hs ht
    let t := flip i s
    have hk : rowTest C (walsh s + walsh t) := by
      apply (kernel_walsh hW _).mpr
      intro z hz
      rw [coefficient_pair]
      have ht' : t ∉ A := ht
      simp [show s ≠ z from fun e => hs (e ▸ hz), show t ≠ z from fun e => ht' (e ▸ hz)]
    have hh : halfSupport i o (walsh s + walsh t) := by
      intro x hx
      have hx' : x i = true := by cases h : x i <;> simp_all [o]
      simp [t, walsh_flip, hx', signBit]
    have := hact o i _ hk hh
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib] at this
    simpa [p, t, eval_finset_sum, mul_comm] using this

private theorem coefficient_flip {q : ℕ} (s : Cube q) {i : Fin q} {u : Cube q}
    {h : Cube q → ℚ} (hh : halfSupport i u h) :
    coefficient (flip i s) h = coefficient s h * signBit true (u i) := by
  unfold coefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [walsh_flip]
  by_cases he : x i = u i
  · rw [he, mul_assoc]
  · simp [hh x he]

private theorem edge_sum {q d : ℕ} {labels : Fin q → ℚ} {A : Set (Cube q)}
    {p : Cube q → ℚ[X]} (hp : edgeCondition labels A d p) (u : Cube q) (i : Fin q)
    (h : Cube q → ℚ) (hk : ∀ s ∈ A, coefficient s h = 0) (hh : halfSupport i u h) :
    (∑ s : Cube q, (p s).eval (labels i) * walsh s u * coefficient s h) = 0 := by
  classical
  let g := fun s : Cube q => (p s).eval (labels i) * walsh s u * coefficient s h
  have hneg (s : Cube q) : g s + g (flip i s) = 0 := by
    simp only [g, walsh_flip, coefficient_flip s hh]
    by_cases hs : s ∈ A
    · simp [hk s hs]
    by_cases ht : flip i s ∈ A
    · have z := hk _ ht
      rw [coefficient_flip s hh] at z
      have he : signBit true (u i) ≠ 0 := by cases hbit : u i <;> norm_num [signBit]
      simp [(mul_eq_zero.mp z).resolve_right he]
    · have he := hp.2.2 i s hs ht
      cases hb : u i <;> simp only [signBit] <;> linear_combination (walsh s u * coefficient s h) * he
  have hz : (∑ s, g s) + (∑ s, g (flip i s)) = 0 := by
    rw [← Finset.sum_add_distrib]
    simp [hneg]
  have he : (∑ s, g (flip i s)) = ∑ s, g s := (flipEquiv i).sum_comp g
  rw [he] at hz
  change ∑ s, g s = 0
  linarith

theorem edges_to_matrix {ι : Type*} {q d : ℕ} {labels : Fin q → ℚ}
    {C : Matrix ι (Cube q) ℚ} {A : Set (Cube q)} (hW : rowSpace C = walshSpace A)
    {p : Cube q → ℚ[X]} (hp : edgeCondition labels A d p) :
    ∃ P, matrixCondition labels C d P := by
  classical
  let D : ℚ := 2^q
  have hd : D ≠ 0 := pow_ne_zero _ (by norm_num)
  let P := fun u v : Cube q =>
    ∑ s : Cube q, Polynomial.C (walsh s u * walsh s v / D) * p s
  refine ⟨P, ?_, ?_, ?_⟩
  · intro u v
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro s _
    exact (natDegree_C_mul_le _ _).trans (hp.1 s)
  · intro u v
    simp only [P, eval_finset_sum, eval_mul, eval_C, hp.2.1, mul_one, ← Finset.sum_div]
    have h : (∑ s : Cube q, walsh s u * walsh s v) = if u = v then D else 0 := by
      calc
        _ = ∑ s : Cube q, walsh u s * walsh v s := by
          apply Finset.sum_congr rfl
          intro s _
          rw [walsh_comm s u, walsh_comm s v]
        _ = _ := walsh_orthogonal u v
    rw [h]
    split <;> simp_all
  · intro u i h hk hh
    have hn := edge_sum hp u i h ((kernel_walsh hW h).mp hk) hh
    calc
      _ = (∑ s : Cube q, (p s).eval (labels i) * walsh s u * coefficient s h) / D := by
        simp only [P, eval_finset_sum, eval_mul, eval_C, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp only [coefficient, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = 0 := by rw [hn, zero_div]

theorem matrix_iff_edges {ι : Type*} {q d : ℕ} (labels : Fin q → ℚ)
    (C : Matrix ι (Cube q) ℚ) (A : Set (Cube q)) (hW : rowSpace C = walshSpace A) :
    (∃ P, matrixCondition labels C d P) ↔ ∃ p, edgeCondition labels A d p :=
  ⟨fun ⟨_,h⟩ => matrix_to_edges hW h, fun ⟨_,h⟩ => edges_to_matrix hW h⟩

end
end LocalReconstruction
