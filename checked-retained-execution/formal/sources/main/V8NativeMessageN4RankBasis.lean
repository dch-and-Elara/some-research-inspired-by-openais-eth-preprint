import V8CapacityUnifiedHybrid
import Mathlib.Algebra.Algebra.Rat

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

/-! A rational native jet need not be an algebra over the larger
common output field. Expand it over its actual Q-basis and move
just its coordinates into the receiving field. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators
noncomputable section

variable {K X Y : Type*} [Field K] [Algebra ℚ K] [Fintype X] [Fintype Y]
variable {J : Type*} [CommRing J] [Algebra ℚ J]

def nativeMixed (read : J→ₗ[ℚ]K) (row : X→J) (col : Y→J) (u : X→K) (v : Y→K) :
    Matrix X Y K := Matrix.of fun x y => read (row x*col y)*(u x*v y)

omit [Fintype X] in
theorem nativeMixed_rank {I : Type*} [Fintype I] (basis : Module.Basis I ℚ J)
    (read : J→ₗ[ℚ]K) (row : X→J) (col : Y→J) (u : X→K) (v : Y→K) :
    (nativeMixed read row col u v).rank≤Fintype.card I := by
  let A : Matrix X I K := Matrix.of (fun x i => algebraMap ℚ K (basis.repr (row x) i)*u x)
  let B : Matrix I Y K := Matrix.of (fun i y => read (basis i*col y)*v y)
  have fact : nativeMixed read row col u v=A*B := by
    ext x y
    simp only [nativeMixed,Matrix.of_apply,Matrix.mul_apply,A,B]
    have e : read (row x*col y)=∑ i, (algebraMap ℚ K (basis.repr (row x) i))*read (basis i*col y) := by
      conv_lhs => rw [← basis.sum_repr (row x)]
      rw [Finset.sum_mul,map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_mul_assoc,LinearMap.map_smul,Algebra.smul_def]
    rw [e,Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [fact]
  exact (Matrix.rank_mul_le_left A B).trans (Matrix.rank_le_card_width A)

omit [Algebra ℚ K] [Fintype X] in
theorem outer_rank (u : X→K) (v : Y→K) :
    (Matrix.of fun x y => u x*v y : Matrix X Y K).rank≤1 := by
  let A : Matrix X (Fin 1) K := Matrix.of fun x _ => u x
  let B : Matrix (Fin 1) Y K := Matrix.of fun _ y => v y
  have he : (Matrix.of fun x y => u x*v y : Matrix X Y K)=A*B := by
    ext x y
    simp [A,B,Matrix.mul_apply]
  rw [he]
  exact (Matrix.rank_mul_le_left A B).trans (by
    simpa only [Fintype.card_fin] using Matrix.rank_le_card_width A)

#print axioms nativeMixed_rank
#print axioms outer_rank
end
end V8NativeMessage.N4
