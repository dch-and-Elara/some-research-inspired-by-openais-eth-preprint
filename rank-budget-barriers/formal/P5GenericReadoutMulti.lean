import P5GenericReadoutBivRep
import P5GenericReadoutGrid

/-! Original double rectangular scalarization of all r groups.
There are exactly (r(k-1)+1)(r(l-1)+1) indexed samples in the
displayed representation; no minimal-sample claim is made. -/
namespace Paper5.GenericReadout
open Polynomial
open scoped BigOperators Polynomial Classical

variable {K G : Type*} [Field K] [Fintype G]

set_option maxRecDepth 2600 in
set_option synthInstance.maxHeartbeats 1200000 in
set_option maxHeartbeats 26000000 in
theorem scalarize_ordinary_bivariate {k l : ℕ} (hk : 0<k)
    (read : P5A2.Simultaneous K k l→ₗ[K]K)
    (x : Fin (Fintype.card G*(k-1)+1)→K) (y : Fin (Fintype.card G*(l-1)+1)→K)
    (hx : Function.Injective x) (hy : Function.Injective y) (u : G→P5A2.Simultaneous K k l) :
    read (∏g,u g) =
      ∑i,∑j,read (bivQuot K k l (tensorBasis (lagrange x i) (lagrange y j))) *
        ∏g,gridEval (x i) (y j) (bivRep k l (u g)) := by
  let Q := bivQuot K k l
  let p (g : G) := bivRep k l (u g)
  have h := ordinary_product_rectangle_degree p (k-1) (l-1)
    (fun g n=>bivRep_inner_degree k l (u g) n) (fun g=>bivRep_outer_degree k l (u g))
  calc
    read (∏g,u g) = read (Q (∏g,p g)) := by
      have hQ : Q (∏g,p g)=∏g,Q (p g) := map_prod Q.toMonoidHom p Finset.univ
      rw [hQ]
      simp only [p,Q,bivRep_mk hk]
    _ = _ := by
      rw [ordinary_interpolate_rectangle x y hx hy _ h.1 h.2]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul Q]
      have he (a : K) : Q (C (C a))=algebraMap K (P5A2.Simultaneous K k l) a := rfl
      rw [he,←Algebra.smul_def,map_smul,smul_eq_mul,mul_comm]
      congr 1
      exact map_prod (gridEval (x i) (y j)) _ _

theorem bivariate_index_count (k l : ℕ) :
    Fintype.card (Fin (Fintype.card G*(k-1)+1) × Fin (Fintype.card G*(l-1)+1)) =
      (Fintype.card G*(k-1)+1)*(Fintype.card G*(l-1)+1) := by simp

def rationalGrid (d : ℕ) : Fin (d+1)→ℚ := fun i=>i.val

theorem rationalGrid_injective (d : ℕ) : Function.Injective (rationalGrid d) := by
  intro i j h
  apply Fin.ext
  change (i.val:ℚ)=j.val at h
  exact_mod_cast h

#print axioms scalarize_ordinary_bivariate
#print axioms bivariate_index_count
#print axioms rationalGrid_injective
end Paper5.GenericReadout
