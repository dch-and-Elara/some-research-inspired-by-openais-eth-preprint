import V8NativeMessageC3HermiteDWeight

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 580000

/-! One lifted field term per actual D address, using the same public
interpolation and quotient decoder as in the native finite computation. -/
namespace V8NativeMessage.C3.Hermite.D
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Integral J6R10Repack
open V8PooledMenu.FiveCopy V8PooledRange
open Canonical
noncomputable section

section Generic
variable {A B K I M J : Type} [CommRing A] [CommRing B] [CommRing K]
  [Fintype I] [Fintype M] [Fintype J]

def modeSum (x : I→M→B) (z : I) : B := ∑ m, x z m
def modeLift (ℓ : B→A) (x : I→M→B) (z : I) : A := ∑ m, ℓ (x z m)

omit [CommRing K] [Fintype I] [Fintype J] in
theorem reduce_modeLift 
    (ρ : A→+*B) (ℓ : B→A) (hℓ : ∀ x, ρ (ℓ x)=x) (x : I→M→B) (z : I) :
    ρ (modeLift ℓ x z)=modeSum x z := by
  simp only [modeLift,modeSum,map_sum,hℓ]

omit [CommRing K] [Fintype J] in
theorem reduce_mode_sum_decode
    (D : (I→B) →ₗ[B] (J→B)) (ρ : A→+* B) (ℓ : B→A)
    (hℓ : ∀ x, ρ (ℓ x)=x) (x : I→M→B) (j : J) :
    ρ (Paper5.D1Literal.liftedCoefficient D ℓ (modeLift ℓ x) j) = D (modeSum x) j := by
  rw [Paper5.D1Literal.reduce_liftedCoefficient D ρ ℓ hℓ]
  exact congrArg (fun b : I→B => D b j) (funext (reduce_modeLift ρ ℓ hℓ x))

theorem modes_exact_field_sum
    (D : (I→B)→ₗ[B](J→B)) (ℓ : B→A) (ψ : A→+*K)
    (W : J→K) (x : I→M→B) :
    (∑ j, W j * ψ (Paper5.D1Literal.liftedCoefficient D ℓ (modeLift ℓ x) j)) =
      ∑ z, ∑ m, Paper5.D1Literal.publicWeight D ℓ ψ W z * ψ (ℓ (x z m)) := by
  calc
    _ = ∑ j, ∑ z, (W j * ψ (ℓ (D (Paper5.D1Literal.probeBasis z) j))) *
        ψ (modeLift ℓ x z) := by
      simp only [Paper5.D1Literal.liftedCoefficient,map_sum,map_mul,Finset.mul_sum,mul_assoc]
    _ = ∑ z, ∑ j, (W j * ψ (ℓ (D (Paper5.D1Literal.probeBasis z) j))) *
        ψ (modeLift ℓ x z) := Finset.sum_comm
    _ = ∑ z, Paper5.D1Literal.publicWeight D ℓ ψ W z * ψ (modeLift ℓ x z) := by
      simp only [Paper5.D1Literal.publicWeight,Finset.sum_mul]
    _ = _ := by simp only [modeLift,map_sum,Finset.mul_sum]
end Generic

variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E}
  {r : ThreePorts G} {f : ℤ[X]}
  (P : Packing G r) (hu : 0<rootU V) (hM : rootU V≤wireSize V)
  (t : Site V) (probes : Probes V f) (hf : f.Monic) (s : V→Bool)

abbrev Modes := ↥(J6RecursiveMenu.menu (high t)
  (J6R10RowAffine.weight (rootIndex hu hM t) (high t) P.mask))

def address (z : Fin (probeCount V)) (β : Modes P hu hM t) : Address P hu hM t :=
  ⟨z,β.val,β.property⟩

def wordAtSlot (z : Fin (probeCount V)) (β : Modes P hu hM t) : Box f 1 (high t) :=
  wholeHigh P hu hM t probes hf s (address P hu hM t z β)

def nativeSamples : Fin (probeCount V)→Box f 1 (high t) :=
  modeSum (wordAtSlot P hu hM t probes hf s)

def liftedWholeSamples : Fin (probeCount V)→IntRing f 1 :=
  modeLift (canonicalLift (high t) f hf 1) (wordAtSlot P hu hM t probes hf s)

theorem liftedWholeSamples_reduce (z : Fin (probeCount V)) :
    reduce (high t) f 1 (liftedWholeSamples P hu hM t probes hf s z) =
      nativeSamples P hu hM t probes hf s z :=
  reduce_modeLift (reduce (high t) f 1) (canonicalLift (high t) f hf 1)
    (canonicalLift_spec (high t) f hf 1) (wordAtSlot P hu hM t probes hf s) z

def liftedDQuotient (j : Fin (dOrder V t)) : IntRing f 1 :=
  Paper5.D1Literal.liftedCoefficient (dDecode V (high t) t probes)
    (canonicalLift (high t) f hf 1) (liftedWholeSamples P hu hM t probes hf s) j

theorem liftedDQuotient_reduce (j : Fin (dOrder V t)) :
    reduce (high t) f 1 (liftedDQuotient P hu hM t probes hf s j) =
      dDecode V (high t) t probes (nativeSamples P hu hM t probes hf s) j :=
  reduce_mode_sum_decode (dDecode V (high t) t probes)
    (reduce (high t) f 1) (canonicalLift (high t) f hf 1)
    (canonicalLift_spec (high t) f hf 1) (wordAtSlot P hu hM t probes hf s) j

theorem whole_D_field_sum :
    (∑ j, dQuotientWeight V f t j * embed f 1 (liftedDQuotient P hu hM t probes hf s j)) =
      ∑ z, ∑ β : Modes P hu hM t, dPublicWeight V t probes hf z *
        embed f 1 (canonicalLift (high t) f hf 1 (wordAtSlot P hu hM t probes hf s z β)) :=
  modes_exact_field_sum (dDecode V (high t) t probes) (canonicalLift (high t) f hf 1)
    (embed f 1) (dQuotientWeight V f t) (wordAtSlot P hu hM t probes hf s)

#print axioms reduce_modeLift
#print axioms reduce_mode_sum_decode
#print axioms modes_exact_field_sum
#print axioms liftedWholeSamples_reduce
#print axioms liftedDQuotient_reduce
#print axioms whole_D_field_sum
end
end V8NativeMessage.C3.Hermite.D
