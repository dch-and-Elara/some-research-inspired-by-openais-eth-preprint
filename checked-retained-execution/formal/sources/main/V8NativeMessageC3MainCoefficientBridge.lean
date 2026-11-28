import V8NativeMessageC3MainCoefficient
import V8NativeMessageC3CanonicalRoot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

namespace V8NativeMessage.C3.RawMain
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive V8PooledMenu.FiveCopy V8PooledRange
open Canonical
noncomputable section
variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ] {G : Graph V E} {r : ThreePorts G}
variable (F : FiveFile (Γ:=Γ) G r) (a : Address F.layout) (k : ℕ)
variable {b : Γ→ℕ} (Q : NativePrivateLists F a k b)
variable {f : ℤ[X]}

/-- Canonical replacement with a genuine extracted MAIN coefficient on
the same five-copy input. Only the D multiplier's loss and the stated
finite margin remain inputs; MAIN loss is derived from its actual
private points, replacement rows and admissible weights. -/
theorem C3_actual_coefficient_replacement
    (hw : ∀ g j, Q.weight g j∈localJetImage k) (j : ℕ)
    (P : Packing G r) (hu : 0<rootU V) (huM : rootU V≤wireSize V) (t : Site V)
    (probes : Probes V f) (hf : f.Monic) (s : V→Bool) (q : V8PooledMenu.FiveCopy.Address P hu huM t)
    (sep : Fin 64→IntRing f 1)
    (hs : ∀ g, reduce (high t) f 1 (sep g)=atRoot P hu huM t probes hf s q g)
    (dMult : RatRing f 1) (hd : HasLoss f 1 (ordinaryDLoss t) dMult)
    (fit : coefficientLoss F ≤ 2*(printedH V*nodeD t)+4*(wireSize V*(rootA V+1))) :
    ∃ e : IntRing f 1, (dMult*algebraMap ℚ (RatRing f 1) (jetCoeff k j (actualRegister F a k Q s)))*
      (embed f 1 (canonicalLift (high t) f hf 1 (wholeHigh P hu huM t probes hf s q)) -
        embed f 1 (∏ g, sep g)) =
        embed f 1 ((2:IntRing f 1)^rootPrec V*e) := by
  exact C3_actual_canonical_replacement P hu huM t probes hf s q sep hs
    (algebraMap ℚ (RatRing f 1) (jetCoeff k j (actualRegister F a k Q s))) dMult
    (coefficient_multiplier_loss F a k Q hw s j f 1) hd fit

#print axioms C3_actual_coefficient_replacement
end
end V8NativeMessage.C3.RawMain