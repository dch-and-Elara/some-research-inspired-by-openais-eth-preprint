import V8NativeMessageC3HermiteDSlot
import V8NativeMessageC3HermiteDEnd

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 780000

/-! The endpoint's cross multiplier is precisely the one obtained from
distributing the ordinary MAIN scalar times the ordinary D readout,
over the actual static probe/mode addresses. -/
namespace V8NativeMessage.C3.Hermite.Native
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Integral
open V8PooledMenu.FiveCopy V8PooledRange
open RawMain Canonical
noncomputable section

variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ]
  {G : Graph V E} {r : ThreePorts G} {f : ℤ[X]}
  (F : FiveFile (Γ:=Γ) G r) (a : RawMain.Address F.layout) {b : Γ→ℕ}
  (Q : NativePrivateLists F a (printedJ F) b)
  (P : Packing G r) (hu : 0<rootU V) (hM : rootU V≤wireSize V)
  (t : Site V) (probes : Probes V f) (hf : f.Monic) (s : V→Bool)

theorem exact_ordinary_cross_expansion :
    algebraMap ℚ (RatRing f 1) (nativeOrigin F a Q s) *
      (∑ j, D.dQuotientWeight V f t j * embed f 1 (D.liftedDQuotient P hu hM t probes hf s j)) =
    ∑ z, ∑ β : D.Modes P hu hM t,
      ordinaryCrossWeight F a Q P hu hM t probes hf s (D.address P hu hM t z β) *
        embed f 1 (canonicalLift (high t) f hf 1
          (wholeHigh P hu hM t probes hf s (D.address P hu hM t z β))) := by
  rw [D.whole_D_field_sum P hu hM t probes hf s]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro β _
  let w := D.dPublicWeight V t probes hf z
  let x := algebraMap ℚ (RatRing f 1) (nativeOrigin F a Q s)
  let y := embed f 1 (canonicalLift (high t) f hf 1 (D.wordAtSlot P hu hM t probes hf s z β))
  change x*(w*y)=(w*x)*y
  ring

/-- One actual ordinary product, with no supplied rank factorization,
obeys the precise termwise transfer at every published D address. -/
theorem every_address_in_ordinary_expansion_is_safe
    (hw : ∀ g j, Q.weight g j∈localJetImage (printedJ F))
    (hQ : F.layout.Q=sourceQ V) {k : ℕ} (hk : 1≤k)
    (hR : F.layout.R=sourceR V k) (h6 : 6*F.layout.R≤F.layout.Q)
    (z : Fin (probeCount V)) (β : D.Modes P hu hM t)
    (lift : Fin 64→IntRing f 1)
    (hlift : ∀ g, reduce (high t) f 1 (lift g) =
      atRoot P hu hM t probes hf s (D.address P hu hM t z β) g) :
    ∃ e : IntRing f 1,
      ordinaryCrossWeight F a Q P hu hM t probes hf s (D.address P hu hM t z β) *
        (embed f 1 (canonicalLift (high t) f hf 1 (D.wordAtSlot P hu hM t probes hf s z β)) -
          embed f 1 (∏ g, lift g)) = embed f 1 ((2:IntRing f 1)^rootPrec V*e) :=
  ordinary_cross_slot_full_printed_guards F a Q P hu hM t probes hf s hw hQ hk hR h6
    (D.address P hu hM t z β) lift hlift

#print axioms exact_ordinary_cross_expansion
#print axioms every_address_in_ordinary_expansion_is_safe
end
end V8NativeMessage.C3.Hermite.Native
