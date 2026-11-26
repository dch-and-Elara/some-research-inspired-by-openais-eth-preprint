import P5A2Powers
import P5A2Box
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.Tactic.FinCases

/-! The displayed rectangular Hankel pairing is evaluated in the real
iterated quotient (K[X]/X^k)[Y]/Y^l. The outer coefficient ring need not be a
domain. -/
namespace P5A2
open Polynomial Matrix Module
open scoped Classical BigOperators

variable {K : Type*} [Field K]

abbrev Double (K : Type*) [Field K] (k l : ℕ) := Trunc (Trunc K k) l

noncomputable def outerPowers (k l : ℕ) (hk : 0<k) :
    Basis (Fin l) (Trunc K k) (Double K k l) :=
  @powers (Trunc K k) inferInstance (trunc_nontrivial K k hk) l

noncomputable def pairBasis (k l : ℕ) (hk : 0<k) : Basis (Fin k × Fin l) K (Double K k l) :=
  (powers K k).smulTower (outerPowers (K:=K) k l hk)

theorem pairBasis_apply {k l : ℕ} (hk : 0<k) (i : Fin k × Fin l) :
    pairBasis (K:=K) k l hk i =
      (algebraMap (Trunc K k) (Double K k l)) (powers K k i.1) *
        outerPowers k l hk i.2 := by
  rw [pairBasis,Basis.smulTower_apply,Algebra.smul_def]

theorem outerPowers_mul {k l : ℕ} (hk : 0<k) (i j : Fin l) :
    outerPowers (K:=K) k l hk i * outerPowers (K:=K) k l hk j =
      if h : i.val+j.val<l then outerPowers (K:=K) k l hk ⟨i.val+j.val,h⟩ else 0 := by
  letI : Nontrivial (Trunc K k) := trunc_nontrivial K k hk
  exact powers_mul (Trunc K k) l i j

set_option maxHeartbeats 3400000 in
theorem pairBasis_mul {k l : ℕ} (hk : 0<k) (i j : Fin k × Fin l) :
    pairBasis (K:=K) k l hk i * pairBasis (K:=K) k l hk j =
      if h : i.1.val+j.1.val < k ∧ i.2.val+j.2.val < l then
        pairBasis (K:=K) k l hk
          (⟨i.1.val+j.1.val,h.1⟩,⟨i.2.val+j.2.val,h.2⟩) else 0 := by
  rw [pairBasis_apply hk i,pairBasis_apply hk j,mul_mul_mul_comm,←map_mul,
    powers_mul,outerPowers_mul]
  by_cases h₁ : i.1.val+j.1.val < k
  · by_cases h₂ : i.2.val+j.2.val < l
    · simp [h₁,h₂,pairBasis_apply]
    · simp [h₁,h₂]
  · simp [h₁]

/-- A general functional has the genuine two-variable Hankel entries;
this does not pretend that the rank of a sum of reads is additive. -/
theorem double_pairing_entry {k l : ℕ} (hk : 0<k) (read : Double K k l →ₗ[K] K)
    (u v : Fin k × Fin l) :
    pairing (pairBasis k l hk) read u v =
      if h : u.1.val+v.1.val < k ∧ u.2.val+v.2.val < l then
        read (pairBasis k l hk
          (⟨u.1.val+v.1.val,h.1⟩,⟨u.2.val+v.2.val,h.2⟩)) else 0 := by
  change read (pairBasis k l hk u * pairBasis k l hk v) = _
  rw [pairBasis_mul]
  split
  · rfl
  · exact map_zero read

/-- A single coefficient selects complementary exponent pairs. -/
theorem double_coordinate_entry {k l : ℕ} (hk : 0<k) (a u v : Fin k × Fin l) :
    pairing (pairBasis (K:=K) k l hk) ((pairBasis (K:=K) k l hk).coord a) u v =
      if u.1.val+v.1.val=a.1.val ∧ u.2.val+v.2.val=a.2.val then 1 else 0 := by
  rw [double_pairing_entry]
  by_cases h : u.1.val+v.1.val=a.1.val ∧ u.2.val+v.2.val=a.2.val
  · have hp : u.1.val+v.1.val<k ∧ u.2.val+v.2.val<l :=
      ⟨h.1.symm ▸ a.1.isLt,h.2.symm ▸ a.2.isLt⟩
    rw [dif_pos hp,if_pos h,coord_basis]
    have he : ((⟨u.1.val+v.1.val,hp.1⟩ : Fin k),(⟨u.2.val+v.2.val,hp.2⟩ : Fin l)) = a :=
      Prod.ext (Fin.ext h.1) (Fin.ext h.2)
    rw [if_pos he]
  · rw [if_neg h]
    split
    · rename_i hp
      rw [coord_basis]
      have hn : ((⟨u.1.val+v.1.val,hp.1⟩ : Fin k),(⟨u.2.val+v.2.val,hp.2⟩ : Fin l)) ≠ a := by
        intro he
        exact h ⟨congrArg (fun p : Fin k × Fin l => p.1.val) he,
          congrArg (fun p : Fin k × Fin l => p.2.val) he⟩
      rw [if_neg hn]
    · rfl

abbrev caps (k l : ℕ) : Fin 2 → ℕ := ![k,l]

def pairEquiv (k l : ℕ) : Box (caps k l) ≃ (Fin k × Fin l) :=
  piFinTwoEquiv (fun i => Fin (caps k l i))

theorem pairExp_iff (k l : ℕ) (a u v : Box (caps k l)) :
    (∀ i, (u i).val+(v i).val=(a i).val) ↔
      ((pairEquiv k l u).1.val+(pairEquiv k l v).1.val=(pairEquiv k l a).1.val ∧
      (pairEquiv k l u).2.val+(pairEquiv k l v).2.val=(pairEquiv k l a).2.val) := by
  constructor
  · intro h
    exact ⟨h 0,h 1⟩
  · intro h i
    fin_cases i
    · exact h.1
    · exact h.2

set_option maxHeartbeats 3900000 in
/-- This is the (a+1)(b+1) rank in Paper 5, in the actual quotient basis. -/
theorem double_coordinate_rank {k l : ℕ} (hk : 0<k) (a : Fin k × Fin l) :
    (pairing (pairBasis (K:=K) k l hk) ((pairBasis (K:=K) k l hk).coord a)).rank =
      (a.1.val+1)*(a.2.val+1) := by
  let M := pairing (pairBasis (K:=K) k l hk) ((pairBasis (K:=K) k l hk).coord a)
  let e := pairEquiv k l
  have he : M.submatrix e e = coordinateMatrix (K:=K) (e.symm a) := by
    apply Matrix.ext
    intro u v
    change M (e u) (e v) = _
    rw [show M (e u) (e v) = _ from double_coordinate_entry hk a (e u) (e v)]
    unfold coordinateMatrix
    rw [Matrix.of_apply]
    have hiff := pairExp_iff k l (e.symm a) u v
    change (∀ i, (u i).val+(v i).val=((e.symm a) i).val) ↔
      (e u).1.val+(e v).1.val=(e (e.symm a)).1.val ∧
        (e u).2.val+(e v).2.val=(e (e.symm a)).2.val at hiff
    rw [e.apply_symm_apply] at hiff
    by_cases h : ∀ i, (u i).val+(v i).val=((e.symm a) i).val
    · rw [if_pos (hiff.mp h),if_pos h]
    · rw [if_neg (fun hh => h (hiff.mpr hh)),if_neg h]
  calc
    M.rank = (M.submatrix e e).rank := (Matrix.rank_submatrix M e e).symm
    _ = ∏ i, (((e.symm a) i).val+1) := by
      rw [he]
      have hs (F G : Fintype (Box (caps k l))) :
          @Matrix.rank _ _ K F _ (coordinateMatrix (e.symm a)) =
            @Matrix.rank _ _ K G _ (coordinateMatrix (e.symm a)) := by
        rw [Subsingleton.elim F G]
      exact (hs _ _).trans (coordinateMatrix_rank (K:=K) (d:=caps k l) (e.symm a))
    _ = _ := by
      rw [Fin.prod_univ_two]
      have h := e.apply_symm_apply a
      change (((e.symm a) 0).val+1)*(((e.symm a) 1).val+1) = _
      rw [show ((e.symm a) 0).val = a.1.val from congrArg (fun p : Fin k × Fin l => p.1.val) h,
        show ((e.symm a) 1).val = a.2.val from congrArg (fun p : Fin k × Fin l => p.2.val) h]

theorem double_top_rank (k l : ℕ) :
    let b := pairBasis (K:=K) (k+1) (l+1) (Nat.succ_pos _)
    (pairing b (b.coord (Fin.last k,Fin.last l))).rank = (k+1)*(l+1) := by
  simpa using (double_coordinate_rank (K:=K) (Nat.succ_pos k) (Fin.last k,Fin.last l))

#print axioms pairBasis_apply
#print axioms pairBasis_mul
#print axioms double_pairing_entry
#print axioms double_coordinate_entry
#print axioms double_coordinate_rank
#print axioms double_top_rank
end P5A2
