import V8CapacityWidthLower
import V8CapacityWidthUpper
import Mathlib.RingTheory.Localization.Module

/-! Passing from a K-factorization of an integral output to a genuine
integral factorization. This is distinct from the operation count of an
algorithm constructing the lift. -/
namespace V8CapacityLift
open scoped Classical BigOperators
open Module V8CapacityCRTJet V8CapacityWidthUpper

noncomputable section
set_option maxHeartbeats 600000

variable {O K I J Y : Type*}
variable [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
variable [Field K] [Algebra O K] [IsFractionRing O K] [Fintype I] [Fintype J]

def liftRows : (I → O) →ₗ[O] (I → K) :=
  LinearMap.pi fun i => (Algebra.linearMap O K).comp (LinearMap.proj i)

omit [IsDomain O] [IsPrincipalIdealRing O] [Fintype I] in
theorem liftRows_injective : Function.Injective (liftRows (O:=O) (K:=K) (I:=I)) := by
  intro a b h
  funext i
  exact IsFractionRing.injective O K (congrFun h i)

def integralPart (A : (J → K) →ₗ[K] (I → K)) :
    Submodule O (I → O) :=
  Submodule.comap liftRows ((LinearMap.range A).restrictScalars O)

/-- Taking the integral points in a K-column space cannot increase its
rank over a PID. In particular the result still holds when none of the
supplied K-factor vectors are integral. -/
theorem integral_factor_through (A : (J → K) →ₗ[K] (I → K))
    (out : Y → (I → O)) (ho : ∀ y, ∃ z, A z=liftRows (out y)) :
    ∃ n ≤ Fintype.card J, ∃ l : I → Fin n → O, ∃ r : Fin n → Y → O,
      ∀ i y, out y i=∑ j : Fin n, l i j * r j y := by
  let T := integralPart (O:=O) A
  obtain ⟨n,S⟩ := T.smithNormalForm (Pi.basisFun O I)
  let G : T →ₗ[O] LinearMap.range A :=
    (liftRows.comp T.subtype).codRestrict ((LinearMap.range A).restrictScalars O)
      (fun y => y.property)
  have hi : Function.Injective G := by
    intro a b h
    exact Subtype.ext (liftRows_injective (congrArg Subtype.val h))
  have hli : LinearIndependent K (G ∘ S.bN) :=
    (LinearIndependent.iff_fractionRing O K).mp
      (S.bN.linearIndependent.map' G (LinearMap.ker_eq_bot.mpr hi))
  have cn := hli.fintype_card_le_finrank
  have nj := LinearMap.finrank_range_le A
  rw [Module.finrank_fintype_fun_eq_card] at nj
  have hi' : n≤Fintype.card J := by
    simpa only [Fintype.card_fin] using cn.trans nj
  let yy (y : Y) : T := ⟨out y,ho y⟩
  refine ⟨n,hi',fun i j => (S.bN j).val i,fun j y => S.bN.repr (yy y) j,?_⟩
  intro i y
  have hh := congrArg (fun w : T => w.val i) (S.bN.sum_repr (yy y))
  simp only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul] at hh
  simpa only [yy,mul_comm] using hh.symm

omit [IsPrincipalIdealRing O] [IsDomain O] [Fintype I] in
theorem quotient_factor_through (π : O) (p : ℕ) (out : Y → I → O)
    (l : I → J → O) (r : J → Y → O)
    (exact : ∀ i y, out y i=∑ j : J, l i j * r j y) :
    ∀ i y, coeffMod O π p (out y i)=
      ∑ j : J, coeffMod O π p (l i j)*coeffMod O π p (r j y) := by
  intro i y
  rw [exact,map_sum]
  simp only [map_mul]

#print axioms liftRows_injective
#print axioms integral_factor_through
#print axioms quotient_factor_through
end
end V8CapacityLift

