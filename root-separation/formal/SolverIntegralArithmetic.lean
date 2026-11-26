import SolverConcreteRoot
import SolverChildren

noncomputable section
namespace RootSeparation.Solver
open scoped BigOperators

variable {e : ℕ} (F : SourcePolynomial e)

/-- Canonical integral subring of the actual fraction-field quotient,
    defined by the proved basis valuation. -/
def integralElements : Subring (RationalRing F.f) where
  carrier := {x | 0 ≤ rationalValuation F x}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' {x y} hx hy := (le_min hx hy).trans ((rationalValuation F).map_add _ _)
  mul_mem' {x y} hx hy := by
    change 0 ≤ rationalValuation F (x*y)
    rw [(rationalValuation F).map_mul]
    exact add_nonneg hx hy
  neg_mem' {x} hx := by
    change 0 ≤ rationalValuation F (-x)
    rwa [(rationalValuation F).map_neg]

def integralRealize : IntegralRing F.f →+* integralElements F :=
  (integralRational F.f).codRestrict (integralElements F) (fun x =>
    (coordinateOrder_nonnegative F.monic F.degree _).2 ⟨x,rfl⟩)

def integralEquiv : IntegralRing F.f ≃+* integralElements F :=
  RingEquiv.ofBijective (integralRealize F) ⟨
    fun x y h => integralRational_injective F.monic (congrArg Subtype.val h),
    fun x => by
      obtain ⟨y,hy⟩ := (coordinateOrder_nonnegative F.monic F.degree x.val).1 x.property
      exact ⟨y,Subtype.ext hy⟩⟩

def reduceElements (p : ℕ) : integralElements F →+* WordRing F.f p :=
  (integralWord F.f p).comp ((integralEquiv F).symm.toRingHom)

theorem reduceElements_spec (p : ℕ) (x : integralElements F) :
    tryWord F.monic p x.val = some (reduceElements F p x) := by
  let y := (integralEquiv F).symm x
  have h : integralRational F.f y = x.val := congrArg Subtype.val ((integralEquiv F).apply_symm_apply x)
  rw [← h,tryWord_integral]
  rfl

theorem reduceElements_int (p : ℕ) (x : IntegerRing F.f) :
    reduceElements F p ⟨integerRational F.f x,rationalValuation_integer F x⟩ =
      fromInteger F.f p x := by
  have h := reduceElements_spec F p ⟨integerRational F.f x,rationalValuation_integer F x⟩
  rw [tryWord_integer,Option.some.injEq] at h
  exact h.symm

section Coefficient

variable {R S : Type*} [CommSemiring R] [CommSemiring S]
variable {Rows Modes : Type*} [Fintype Rows] [Fintype Modes]

theorem map_packetCoeff (φ : R →+* S) (row : Rows → Option Modes → R) (β : Modes → ℕ) :
    φ (packetCoeff row β) = packetCoeff (fun r z => φ (row r z)) β := by
  classical
  unfold packetCoeff
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro c _
  split <;> simp [*,map_prod]

theorem map_packetValue {Reads : Type*} [Fintype Reads]
    (φ : R →+* S) (row : Rows → Option Modes → R) (β : Modes → ℕ)
    (read : Reads → R) (powers : Reads → ℕ) :
    φ (packetValue row β read powers) =
      packetValue (fun r z => φ (row r z)) β (fun z => φ (read z)) powers := by
  simp [packetValue,map_packetCoeff,map_prod,map_pow]

end Coefficient

#print axioms integralEquiv
#print axioms reduceElements_spec
#print axioms map_packetValue

end RootSeparation.Solver
