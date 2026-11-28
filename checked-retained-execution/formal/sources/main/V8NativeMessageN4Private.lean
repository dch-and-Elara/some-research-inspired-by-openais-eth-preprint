import V8NativeMessageN4Local
import V8NativeMessageN4RankBasis
import V8NativeMessageN6MainLocal
import V8NativeMessageC3Native

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4400000

/-! N3/N4 for the actual four-copy MAIN address and sign-independent
private lists. The common cut can split pins inside a MAIN group.
The prefix is the actual quotient, not a dimension assumption. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open Polynomial Paper5.D1Literal
open V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

def shrink {k J : ℕ} (h : k≤J) : Jet J→ₐ[ℚ]Jet k :=
  AdjoinRoot.algHomOfDvd (X^J) (X^k) (pow_dvd_pow X h)

variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)}
  {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]}
  {P : RootPacking F reg f} {i : rootKept F f}
  {A : Type*} [Field A] [LinearOrder A] {γ : A}
  (C : FourCut P i γ)
variable {R : Type*} [Field R] [Algebra ℚ R]

structure Block (P : RootPacking F reg f) (i : rootKept F f) (R : Type*)
    [Field R] [Algebra ℚ R] where
  groups : ℕ
  nodes : ℕ
  order : ℕ
  kept : ℕ
  tuple : CloneTuple F groups nodes order
  accepted : feasible tuple.frame
  points : N6.FixedLists tuple
  keep : kept≤order
  read : Jet kept→ₗ[ℚ]R
  coefficient : R
  dFactors : LocalFactors P i R

variable (B : Block P i R)

abbrev Choices := ∀ g : Fin B.groups, Fin (B.points.count g)

def privateCapacity : ℕ := B.kept*∏ g, B.points.count g

def mainValue (σ : W→Bool) : R :=
  B.read (shrink B.keep (N6.completed B.tuple reg B.accepted B.points σ))

def sourceValue (σ : W→Bool) : R :=
  B.coefficient*mainValue B σ*nativeD B.dFactors σ

def leftMain (q : Choices B) (x : Fin C.m→Bool) : Jet B.kept :=
  shrink B.keep (∏ g, N6.leftPoint B.tuple reg B.accepted B.points g (q g) (leftSide C) (leftWord C x))

def rightMain (q : Choices B) (y : Fin C.m→Bool) : Jet B.kept :=
  shrink B.keep (∏ g, N6.rightPoint B.tuple reg B.accepted B.points g (q g) (leftSide C) (rightWord C y))

theorem completed_choices (σ : W→Bool) :
    N6.completed B.tuple reg B.accepted B.points σ =
      ∑ q : Choices B, ∏ g, N6.entry B.tuple reg B.accepted B.points g (q g) σ := by
  unfold N6.completed N6.groupJet
  exact Fintype.prod_sum (fun g j => N6.entry B.tuple reg B.accepted B.points g j σ)

theorem choice_factors (q : Choices B) (x y : Fin C.m→Bool) :
    shrink B.keep (∏ g, N6.entry B.tuple reg B.accepted B.points g (q g) (restriction C.pairs x y)) =
      leftMain C B q x*rightMain C B q y := by
  unfold leftMain rightMain
  rw [← map_mul,← Finset.prod_mul_distrib]
  apply congrArg (shrink B.keep)
  apply Finset.prod_congr rfl
  intro g _
  rw [← N6.point_factors]
  exact congrArg (fun σ => N6.entry B.tuple reg B.accepted B.points g (q g) σ)
    (restriction_splice C x y).symm

def blockMatrix : Matrix (Fin C.m→Bool) (Fin C.m→Bool) R :=
  Matrix.of fun x y => sourceValue B (restriction C.pairs x y)

def rankTerm (q : Choices B) : Matrix (Fin C.m→Bool) (Fin C.m→Bool) R :=
  nativeMixed B.read (leftMain C B q) (rightMain C B q)
    (fun x => B.coefficient*leftD C B.dFactors x) (rightD C B.dFactors)

theorem block_expands :
    blockMatrix C B=∑ q : Choices B, rankTerm C B q := by
  ext x y
  simp only [blockMatrix,Matrix.of_apply,Matrix.sum_apply,rankTerm,nativeMixed,sourceValue,mainValue]
  rw [completed_choices,true_D_cut C B.dFactors x y,map_sum,map_sum,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [choice_factors C B q x y]
  ring

theorem actual_block_rank :
    (blockMatrix C B).rank≤privateCapacity B := by
  rw [block_expands]
  apply (V8CapacityUnified.U7.rank_sum_le Finset.univ _).trans
  calc
    _ ≤ ∑ _ : Choices B, B.kept := by
      apply Finset.sum_le_sum
      intro q _
      simpa only [rankTerm,Fintype.card_fin] using
        nativeMixed_rank (V8NativeMessage.C3.jetBasis ℚ B.kept) B.read (leftMain C B q) (rightMain C B q)
          (fun x => B.coefficient*leftD C B.dFactors x) (rightD C B.dFactors)
    _ = _ := by simp [privateCapacity,Choices,Fintype.card_pi,Nat.mul_comm]

omit [Algebra ℚ R] in
theorem pure_D_rank (D : LocalFactors P i R) (c : R) :
    (Matrix.of (fun x y : Fin C.m→Bool => c*nativeD D (restriction C.pairs x y)) :
      Matrix (Fin C.m→Bool) (Fin C.m→Bool) R).rank≤1 := by
  have he : (Matrix.of (fun x y : Fin C.m→Bool => c*nativeD D (restriction C.pairs x y)) :
      Matrix (Fin C.m→Bool) (Fin C.m→Bool) R) = Matrix.of (fun x y =>
        (c*leftD C D x)*rightD C D y) := by
    ext x y
    simp only [Matrix.of_apply,true_D_cut C D x y,mul_assoc]
  rw [he]
  exact outer_rank _ _

#print axioms completed_choices
#print axioms choice_factors
#print axioms block_expands
#print axioms actual_block_rank
#print axioms pure_D_rank
end
end V8NativeMessage.N4
