
import J9R18CompiledReadout
import Mathlib.LinearAlgebra.Lagrange

/-!
An explicit inverse-moment decoder using the coefficients of products of
linear factors. This avoids computing an abstract matrix inverse or
determinant via an exponential permutation expansion.
-/
namespace J9R18Compiled
open scoped Polynomial BigOperators Classical
open Polynomial J8Physical J8J9Grouped J8EndToEnd LiteralPortCompiler
noncomputable section
set_option linter.unusedSectionVars false

section Stencil
variable {K : Type*} [Field K] {n : ℕ}

def stencil (coord : Fin n→K) (i : Fin n) : K[X] :=
  Lagrange.basis Finset.univ coord i

def stencilInverse (coord observed : Fin n→K) (i : Fin n) : K :=
  ∑ b : Fin n, (stencil coord i).coeff b * observed b

theorem stencil_eval_as_dot (coord : Fin n→K) (inj : Function.Injective coord) (i j : Fin n) :
    (∑ b : Fin n, (stencil coord i).coeff b * coord j^(b:ℕ)) =
      if i=j then 1 else 0 := by
  have hdeg : (stencil coord i).natDegree<n := by
    unfold stencil
    have h := Lagrange.natDegree_basis (s:=Finset.univ) (v:=coord)
      inj.injOn (Finset.mem_univ i)
    rw [Finset.card_univ,Fintype.card_fin] at h
    have hi := i.isLt
    omega
  rw [Fin.sum_univ_eq_sum_range (fun b : ℕ => (stencil coord i).coeff b * coord j^b),
    ← Polynomial.eval_eq_sum_range' hdeg]
  by_cases h : i=j
  · subst j
    simp only [stencil]
    exact Lagrange.eval_basis_self inj.injOn (Finset.mem_univ i)
  · rw [if_neg h]
    exact Lagrange.eval_basis_of_ne h (Finset.mem_univ j)

theorem stencilInverse_moments (coord mass : Fin n→K) (inj : Function.Injective coord) :
    stencilInverse coord (NativeMomentReconstruction.moments coord mass) = mass := by
  funext i
  unfold stencilInverse NativeMomentReconstruction.moments
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h (j : Fin n) :
      (∑ b : Fin n, (stencil coord i).coeff b * (mass j * coord j^(b:ℕ))) =
        mass j * (if i=j then 1 else 0) := by
    rw [← stencil_eval_as_dot coord inj i j, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  simp only [h,mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,if_true]

/-- Agreement extends to arbitrary exact observed vectors: the old
Vandermonde inverse is two-sided on distinct coordinates. -/
theorem stencilInverse_exact (coord observed : Fin n→K) (inj : Function.Injective coord) :
    stencilInverse coord observed = NativeMomentReconstruction.invertMoments coord observed := by
  let V := Matrix.vandermonde coord
  let mass := NativeMomentReconstruction.invertMoments coord observed
  have hdet : IsUnit V.det :=
    isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr inj)
  have hs : NativeMomentReconstruction.moments coord mass = observed := by
    change Matrix.vecMul (Matrix.vecMul observed V⁻¹) V = observed
    rw [Matrix.vecMul_vecMul,Matrix.nonsing_inv_mul _ hdet,Matrix.vecMul_one]
  calc
    stencilInverse coord observed = stencilInverse coord (NativeMomentReconstruction.moments coord mass) :=
      congrArg (stencilInverse coord) hs.symm
    _ = mass := stencilInverse_moments coord mass inj

def stencilDecodeBits (coord scale background observed : Fin n→K) (i : Fin n) : Bool :=
  decide (stencilInverse coord (fun b => observed b / scale b - background b) i=1)

theorem stencilDecodeBits_exact (coord scale background observed : Fin n→K)
    (inj : Function.Injective coord) :
    stencilDecodeBits coord scale background observed =
      NativeMomentReconstruction.decodeBits coord scale background observed := by
  funext i
  unfold stencilDecodeBits NativeMomentReconstruction.decodeBits NativeMomentReconstruction.decode
  rw [stencilInverse_exact _ _ inj]
end Stencil

variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

def stencilReadTile (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S)
    (obs : Fin (Fintype.card (PinTile d a))→ℚ) :
    Fin (Fintype.card (PinTile d a))→Bool :=
  stencilDecodeBits (coordinates d a)
    (fun n => scale d e he F a n) (fun n => background d e he F a n) obs

theorem stencilReadTile_exact (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S)
    (obs : Fin (Fintype.card (PinTile d a))→ℚ) :
    stencilReadTile d e he F a obs = readTile d e he F a obs :=
  stencilDecodeBits_exact _ _ _ _ (coordinates_injective d a)

def stencilReadAll (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (obs : J9R17AllPins.Orders d→ℚ) : S→Bool := fun s =>
  let w := (J9R17AllPins.orderPin d).symm s
  stencilReadTile d e he F (J9R17AllPins.anchor d w.1) (fun n => obs ⟨w.1,n⟩) w.2

theorem stencilReadAll_exact (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (obs : J9R17AllPins.Orders d→ℚ) :
    stencilReadAll d e he F obs = readAll d e he F obs := by
  funext s
  unfold stencilReadAll readAll
  dsimp only
  rw [stencilReadTile_exact]

theorem stencil_compiled_recovers_all (e : EndpointSeating d) (he : Even L) (hL : 2<L)
    (F : OldTables d) (sign : S→Bool)
    (off : ∀ s, d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (sat : ∀ g v, ∃ x, satisfied (F g v) x=true) :
    stencilReadAll d e he F (fun w => firstCoefficient d e he F (J9R17AllPins.anchor d w.1) w.2 sign) =
      sign := by
  rw [stencilReadAll_exact]
  exact compiled_recovers_all d e he hL F sign off sat

#print axioms stencil_eval_as_dot
#print axioms stencilInverse_moments
#print axioms stencilInverse_exact
#print axioms stencilDecodeBits_exact
#print axioms stencilReadTile_exact
#print axioms stencilReadAll_exact
#print axioms stencil_compiled_recovers_all

end
end J9R18Compiled
