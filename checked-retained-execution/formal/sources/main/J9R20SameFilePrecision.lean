
import J9R20SameFilePublicTransport
import J9R17AllPinsDecode

/-! At the high boundary the postprocessor needs only 10M coefficient
bits of the same returned box, not a recompiled 10M-bit root or mode. -/
namespace J9R20SameFile
open scoped Polynomial Classical
open Polynomial NativeProbeRing J6R9Recursive J6R10Integral J6R14SpecializedBox
open J9R15FrozenErasurePrecision J9R17AllPins J8Physical J8EndToEnd J8J9Grouped
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2700000

theorem atZero_commutes_with_lower_box (p q : ℕ) (hqp : q≤p) (f : ℤ[X])
    (ell : ℕ) (hℓ : 0<ell) (x : Box f ell p) :
    atZero q f ell hℓ (lowerBox p q hqp f ell x) =
      NativeProbeRing.reduceScalar q p hqp f (atZero p f ell hℓ x) := by
  obtain ⟨p₀,rfl⟩ := AdjoinRoot.mk_surjective x
  simp only [lowerBox,adjoinMap_mk,atZero,AdjoinRoot.lift_mk,Polynomial.eval₂_at_zero,
    Polynomial.coeff_map,RingHom.id_apply,lowerScalar]

variable {Packet R S V G : Type} {U : V→Type} {L M : ℕ}
variable (d : Layout Packet R S V G U L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v,Fintype (U v)]

def readAtTenM (pin : S) (idx : Wire R≃Fin M)
    (n : Fin (Fintype.card (PinTile d pin)))
    (f : ℤ[X]) (hf : f.Monic) (fit : 10*M+1≤2^f.natDegree) (Mpos : 0<M)
    (y : Fin (10*M+1)→Scalar (10*M) f) : ℚ :=
  let U := J9FactorBounds.publicDenominator (J9End.chart d pin idx (fun _ => false)) n
  let x := fun i => probe (10*M) f (chosenRep f.natDegree (10*M+1) fit i)
  ((projectBase (10*M) f hf ((U:Scalar (10*M) f) *
    NativeInterpolation.decode x y ⟨1,by omega⟩)).valMinAbs : ℚ) / U

theorem public_coefficient_factors_through_10M (pin : S) (idx : Wire R≃Fin M)
    (n : Fin (Fintype.card (PinTile d pin)))
    (p ell : ℕ) (hP : 10*M≤p) (hℓ : 0<ell) (f : ℤ[X]) (hf : f.Monic)
    (fit : 10*M+1≤2^f.natDegree) (Mpos : 0<M) (recv : Fin (10*M+1)→Box f ell p) :
    publicCoefficient d pin idx n p ell hP hℓ f hf fit Mpos recv =
      readAtTenM d pin idx n f hf fit Mpos
        (fun i => atZero (10*M) f ell hℓ (lowerBox p (10*M) hP f ell (recv i))) := by
  unfold publicCoefficient readAtTenM
  simp only [atZero_commutes_with_lower_box]

#print axioms atZero_commutes_with_lower_box
#print axioms readAtTenM
#print axioms public_coefficient_factors_through_10M
end
end J9R20SameFile
