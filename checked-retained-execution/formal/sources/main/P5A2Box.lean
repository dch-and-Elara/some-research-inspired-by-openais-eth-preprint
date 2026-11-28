import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.Pi

/-! A coordinate readout sees exactly the complementary pairs of a
multivariate monomial box, for arbitrarily many finite coordinates. -/
namespace P5A2
open Matrix
open scoped BigOperators Classical

variable {K : Type*} [Field K]

theorem partial_permutation_rank {I : Type*} [Fintype I] [DecidableEq I] (P : I → Prop)
    (e : Equiv.Perm I) :
    (Matrix.of (fun i j => if P i ∧ e i=j then (1:K) else 0)).rank =
      Fintype.card {i // P i} := by
  let H : Matrix I I K := Matrix.of (fun i j => if P i ∧ e i=j then 1 else 0)
  have he : H.submatrix (Equiv.refl I) e = diagonal (fun i => if P i then (1:K) else 0) := by
    apply Matrix.ext
    intro i j
    change (if P i ∧ e i=e j then (1:K) else 0) = _
    by_cases h : i=j
    · subst j
      simp
    · simp [h,e.injective.ne h]
  change H.rank = _
  rw [← Matrix.rank_submatrix H (Equiv.refl I) e,he,Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by by_cases h : P i <;> simp [h]))

variable {I : Type*} [Fintype I]

abbrev Box (d : I → ℕ) := (i : I) → Fin (d i)

def active {d : I → ℕ} (a u : Box d) : Prop := ∀ i, (u i).val ≤ (a i).val

/-- On the active coordinatewise interval this subtracts from the fixed
monomial's exponent; outside that interval it is the identity. -/
noncomputable def complement {d : I → ℕ} (a u : Box d) : Box d :=
  if active a u then fun i => ⟨(a i).val-(u i).val,
    (Nat.sub_le ..).trans_lt (a i).isLt⟩ else u

omit [Fintype I] in
theorem complement_val {d : I → ℕ} (a u : Box d) (h : active a u) (i : I) :
    ((complement a u) i).val = (a i).val-(u i).val := by
  rw [complement, if_pos h]

omit [Fintype I] in
theorem complement_active {d : I → ℕ} (a u : Box d) (h : active a u) :
    active a (complement a u) := by
  intro i
  simp [complement,h]

omit [Fintype I] in
theorem complement_involutive {d : I → ℕ} (a : Box d) :
    Function.Involutive (complement a) := by
  intro u
  by_cases h : active a u
  · have h' := complement_active a u h
    funext i
    apply Fin.ext
    rw [complement_val a (complement a u) h' i,complement_val a u h i]
    have hh := h i
    omega
  · simp [complement,h]

omit [Fintype I] in
theorem sum_exponents_iff {d : I → ℕ} (a u v : Box d) :
    (∀ i, (u i).val+(v i).val=(a i).val) ↔ active a u ∧ complement a u=v := by
  constructor
  · intro h
    have hx : active a u := fun i => by have hi := h i; omega
    refine ⟨hx,?_⟩
    funext i
    apply Fin.ext
    simp only [complement,if_pos hx]
    have hh := h i
    omega
  · rintro ⟨h,rfl⟩
    intro i
    simp only [complement,if_pos h]
    have hh := h i
    omega

theorem card_active {d : I → ℕ} (a : Box d) :
    Fintype.card {u : Box d // active a u} = ∏ i, ((a i).val+1) := by
  let e : {u : Box d // active a u} ≃ ((i : I) → Fin ((a i).val+1)) :=
    { toFun := fun u i => ⟨(u.val i).val,Nat.lt_succ_of_le (u.property i)⟩
      invFun := fun w => ⟨fun i => ⟨(w i).val,(Nat.le_of_lt_succ (w i).isLt).trans_lt (a i).isLt⟩,
        fun i => Nat.le_of_lt_succ (w i).isLt⟩
      left_inv := fun u => Subtype.ext (funext fun i => Fin.ext rfl)
      right_inv := fun w => funext fun i => Fin.ext rfl }
  rw [Fintype.card_congr e,Fintype.card_pi]
  simp

/-- Exact rank for one monomial coefficient, even at zero coordinates
or for an empty box of variables (the ground field). -/
noncomputable def coordinateMatrix {d : I → ℕ} (a : Box d) : Matrix (Box d) (Box d) K :=
  Matrix.of fun u v => if ∀ i, (u i).val+(v i).val=(a i).val then 1 else 0

theorem coordinateMatrix_rank {d : I → ℕ} (a : Box d) :
    (coordinateMatrix (K:=K) a).rank = ∏ i, ((a i).val+1) := by
  let e : Equiv.Perm (Box d) := (complement_involutive a).toPerm _
  have he : coordinateMatrix (K:=K) a =
      Matrix.of (fun u v => if active a u ∧ e u=v then (1:K) else 0) := by
    apply Matrix.ext
    intro u v
    change (if ∀ i, (u i).val+(v i).val=(a i).val then 1 else 0) =
      (if active a u ∧ complement a u=v then 1 else 0)
    by_cases h : ∀ i, (u i).val+(v i).val=(a i).val
    · rw [if_pos h,if_pos ((sum_exponents_iff a u v).mp h)]
    · rw [if_neg h,if_neg (fun hh => h ((sum_exponents_iff a u v).mpr hh))]
  rw [he]
  exact (partial_permutation_rank (K:=K) (active a) e).trans (card_active a)

#print axioms partial_permutation_rank
#print axioms complement_involutive
#print axioms sum_exponents_iff
#print axioms card_active
#print axioms coordinateMatrix_rank
end P5A2
