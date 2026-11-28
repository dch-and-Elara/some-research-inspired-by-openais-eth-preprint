import J1R14QueryFibre
import NativeJ2

/-! Glue for the source numerical query. This converts ordered finite tape
indices to the physical node, variable and (group, copy, basis-row)
addresses. The non-pin factor evaluator is still a separate input
interface: this module does not price or assume its correctness. -/
namespace J1R14Query
open scoped BigOperators Polynomial
open MainProbe

universe u v w c b
variable {I : Type u} {S : Type v} {X : Type w} {Copy : Type c}
  {Basis : Type b} {k Q n m D q : ℕ}
variable [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  [Fintype X] [DecidableEq X] [Fintype Copy] [Fintype Basis]
variable (L : DiagonalLayout I S X Copy (Fin k))
variable (B : BasisFile (Basis:=Basis) L)

def numericalRows (rho : (S × (Copy × Basis)) ≃ Fin m)
    (y : Fin m → Box D) : RowValues S Copy Basis := fun g h => boxValue (y (rho (g,h)))

omit [Fintype S] [DecidableEq S] [Fintype Copy] [Fintype Basis] in
theorem numericalRows_bounded (rho : (S × (Copy × Basis)) ≃ Fin m)
    (y : Fin m → Box D) (g : S) (h : Copy × Basis) :
    -(D:ℤ) ≤ numericalRows rho y g h ∧ numericalRows rho y g h ≤ D :=
  boxValue_bounds (y (rho (g,h)))

def indicator (U : Finset (Fin n)) (p : Fin n ≃ X) (x : X) : Bool :=
  decide (p.symm x ∈ U)

noncomputable def compileAddress
    (nu : Fin Q ≃ I) (pi : Fin n ≃ X) (rho : (S × (Copy × Basis)) ≃ Fin m)
    (a : Address Q n m D q)
    (other : (Fin k → Bool) → Bool → S → (X → Bool) → ℚ[X]) : NativeJ2.Address I S X k where
  node := nu a.t
  fixed := prescribed L B (nu a.t) (numericalRows rho a.y)
  fibre := fun g => secondScan L B (nu a.t) g (a.E.map pi.toEmbedding) (numericalRows rho a.y)
  direction := indicator a.U pi
  other := other

theorem compileAddress_group
    (nu : Fin Q ≃ I) (pi : Fin n ≃ X) (rho : (S × (Copy × Basis)) ≃ Fin m)
    (a : Address Q n m D q)
    (other : (Fin k → Bool) → Bool → S → (X → Bool) → ℚ[X])
    (interval : Finset ℕ) (hOutside : 0 ∉ interval) (f : ℚ[X]) (node : I → ℚ)
    (g : S) (sigma : Fin k → Bool) (b : Bool) :
    let ad := compileAddress L B nu pi rho a other
    sourceGroupProbe L interval f node ad.node g Finset.univ
      (ad.fibre g) ad.direction ad.fixed sigma (ad.other sigma b g) =
    ∑ x ∈ secondScan L B (nu a.t) g (a.E.map pi.toEmbedding) (numericalRows rho a.y),
      other sigma b g x * ∏ p ∈ ownedPins L (nu a.t) g Finset.univ,
        pinFactor (sigma p) (correctedArgument (sourceRow f node (L.slot p)) (node (nu a.t))
          (embedded L (L.copy p) (fun j => boolRat (x j)))
          (embedded L (L.copy p) (fun j => boolRat (indicator a.U pi j)))) := by
  exact original_group_sum L B interval hOutside f node (nu a.t) g
    (a.E.map pi.toEmbedding) (numericalRows rho a.y) Finset.univ
    (indicator a.U pi) sigma (other sigma b g)

/-- The completed address also agrees with the source empty-tuple policy:
it returns zero as a polynomial if even one unrestricted local fibre is empty.
This does not construct or price the representative chosen in other groups. -/
theorem compileAddress_skipped
    (nu : Fin Q ≃ I) (pi : Fin n ≃ X) (rho : (S × (Copy × Basis)) ≃ Fin m)
    (a : Address Q n m D q)
    (other : (Fin k → Bool) → Bool → S → (X → Bool) → ℚ[X])
    (interval : Finset ℕ) (f : ℚ[X]) (node : I → ℚ)
    (g : S) (h : firstScan L B (nu a.t) g (numericalRows rho a.y) = ∅)
    (sigma : Fin k → Bool) (b : Bool) :
    let ad := compileAddress L B nu pi rho a other
    sourceCompletedProbe L interval f node ad.node Finset.univ
      ad.fibre ad.direction ad.fixed sigma (ad.other sigma b) = 0 := by
  classical
  dsimp [compileAddress,sourceCompletedProbe]
  apply Finset.prod_eq_zero (Finset.mem_univ g)
  simp [sourceGroupProbe,secondScan,h]

#print axioms numericalRows_bounded
#print axioms compileAddress_group
#print axioms compileAddress_skipped
end J1R14Query
