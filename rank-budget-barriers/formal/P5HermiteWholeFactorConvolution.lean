import P5HermiteTransportGenericProduct
import Mathlib.LinearAlgebra.Matrix.Rank

/-! For literal polynomial matrices, the coefficient-first operator in
the archived H.3 is multiplicative after truncation. Its inner dimension
for a width-r polynomial factor is exactly k times r coordinates. -/
namespace Paper5.HermiteWholeFactor
open Polynomial Matrix
open Paper5.HermiteGeneric (convolution convolution_apply)
open scoped BigOperators Polynomial Classical

variable {R : Type*} [CommRing R]

noncomputable def windowCoeff (p : R[X]) {k : ℕ} (r l : Fin k) : R :=
  if l.val ≤ r.val then p.coeff (r.val-l.val) else 0

theorem windowCoeff_sum {J : Type*} [Fintype J] {k : ℕ}
    (P : J→R[X]) (r l : Fin k) :
    windowCoeff (∑ j,P j) r l=∑ j,windowCoeff (P j) r l := by
  by_cases h : l.val≤r.val
  · simp [windowCoeff,h,Polynomial.finset_sum_coeff]
  · simp [windowCoeff,h]

theorem windowCoeff_mul {k : ℕ} (p q : R[X]) (r l : Fin k) :
    windowCoeff (p*q) r l=∑ m : Fin k,windowCoeff p r m * windowCoeff q m l := by
  classical
  by_cases h : l.val≤r.val
  · rw [windowCoeff,if_pos h]
    calc
      _ = ∑ m ∈ (Finset.univ : Finset (Fin k)).filter
          (fun m=>l.val≤m.val ∧ m.val≤r.val),
          p.coeff (r.val-m.val) * q.coeff (m.val-l.val) := by
        rw [Polynomial.coeff_mul]
        let f (a : ℕ×ℕ) (ha : a∈Finset.antidiagonal (r.val-l.val)) : Fin k :=
          ⟨l.val+a.2,by
              have ha' := Finset.mem_antidiagonal.mp ha
              have hr := r.isLt
              omega⟩
        refine Finset.sum_bij f ?_ ?_ ?_ ?_
        · intro a ha
          have ha' := Finset.mem_antidiagonal.mp ha
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by dsimp [f]; omega⟩
        · intro a ha b hb he
          have ha' := Finset.mem_antidiagonal.mp ha
          have hb' := Finset.mem_antidiagonal.mp hb
          have hev := congrArg Fin.val he
          change l.val+a.2=l.val+b.2 at hev
          exact Prod.ext (by omega) (by omega)
        · intro m hm
          obtain ⟨_,hml,hmr⟩ := Finset.mem_filter.mp hm
          let a := (r.val-m.val,m.val-l.val)
          have ha : a∈Finset.antidiagonal (r.val-l.val) := Finset.mem_antidiagonal.mpr (by
            dsimp [a]
            omega)
          exact ⟨a,ha,Fin.ext (by dsimp [f,a];omega)⟩
        · intro a ha
          have ha' := Finset.mem_antidiagonal.mp ha
          have ha1 : r.val-(f a ha).val=a.1 := by dsimp [f]; omega
          have ha2 : (f a ha).val-l.val=a.2 := by dsimp [f]; omega
          rw [ha1,ha2]
      _ = _ := by
        rw [Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro m _
        by_cases hmr : m.val≤r.val <;> by_cases hml : l.val≤m.val <;>
          simp [windowCoeff,hmr,hml]
  · rw [windowCoeff,if_neg h]
    symm
    apply Finset.sum_eq_zero
    intro m _
    by_cases hmr : m.val≤r.val
    · have hml : ¬ l.val≤m.val := by omega
      simp [windowCoeff,hml]
    · simp [windowCoeff,hmr]

variable {U V W : Type*}

def truncatedCoefficients {k : ℕ} (P : Matrix U V R[X]) : Fin k→Matrix U V R :=
  fun j=>Matrix.of fun u v=>(P u v).coeff j.val

theorem convolution_polynomial_entry {k : ℕ} (P : Matrix U V R[X])
    (r l : Fin k) (u : U) (v : V) :
    convolution (truncatedCoefficients P) (r,u) (l,v)=windowCoeff (P u v) r l := by
  rw [convolution_apply]
  rfl

theorem convolution_polynomial_mul [Fintype V] {k : ℕ}
    (A : Matrix U V R[X]) (B : Matrix V W R[X]) :
    convolution (k:=k) (truncatedCoefficients (A*B)) =
      convolution (truncatedCoefficients A)*convolution (truncatedCoefficients B) := by
  classical
  apply Matrix.ext
  rintro ⟨r,u⟩ ⟨l,w⟩
  simp only [convolution_polynomial_entry,Matrix.mul_apply,Fintype.sum_prod_type,windowCoeff_sum]
  simp_rw [windowCoeff_mul]
  exact Finset.sum_comm

theorem truncatedCoefficients_map {K : Type*} [CommRing K]
    (f : R→+*K) {k : ℕ} (A : Matrix U V R[X]) :
    (fun j : Fin k=>(truncatedCoefficients A j).map f) =
      truncatedCoefficients (A.map (Polynomial.mapRingHom f)) := by
  funext j
  ext u v
  exact (Polynomial.coeff_map f j.val).symm

variable {K : Type*} [Field K]

theorem polynomial_factor_convolution_rank [Fintype V] [Fintype W] (k : ℕ)
    (A : Matrix U V K[X]) (B : Matrix V W K[X]) :
    (convolution (k:=k) (truncatedCoefficients (A*B))).rank ≤ k*Fintype.card V := by
  rw [convolution_polynomial_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (by
    simpa only [Fintype.card_prod,Fintype.card_fin] using
      Matrix.rank_le_card_width (convolution (k:=k) (truncatedCoefficients A)))

#print axioms windowCoeff_sum
#print axioms windowCoeff_mul
#print axioms convolution_polynomial_entry
#print axioms convolution_polynomial_mul
#print axioms truncatedCoefficients_map
#print axioms polynomial_factor_convolution_rank
end Paper5.HermiteWholeFactor
