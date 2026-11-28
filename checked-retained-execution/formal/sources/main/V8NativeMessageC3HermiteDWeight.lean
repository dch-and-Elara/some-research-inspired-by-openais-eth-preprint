import V8NativeMessageC3HermiteDProbe
import P5D1LiteralDecoder

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000

/-! The tested D schedule loss and the linear finite receiver are
instantiated at the actual five-copy probe list. The field coefficient
for a raw address lifts only the public decoder-basis coefficient. -/
namespace V8NativeMessage.C3.Hermite.D
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6R9Recursive J6R10Integral
open V8PooledMenu V8PooledMenu.FiveCopy V8PooledRange
open Canonical
noncomputable section

variable (V : Type) [Fintype V]

def dNormal (f : ℤ[X]) (p : ℕ) (t : Site V) : (Box f 1 p)[X] :=
  (integralE f 1 (rootA V) (wireSize V) (rootU V) t.val).map (reduce p f 1)

def dDecode {f : ℤ[X]} (p : ℕ) (t : Site V) (probes : Probes V f) :
    (Fin (probeCount V)→Box f 1 p) →ₗ[Box f 1 p]
      (Fin (dOrder V t)→Box f 1 p) :=
  let R := Box f 1 p
  let D : (Fin (probeCount V)→R) →ₗ[R] (ℕ→R) :=
    Paper5.D1Literal.nativeDecoder (dNode V p t probes) (dOrder V t) (dNormal V f p t)
  { toFun := fun x j => D x j.val
    map_add' := fun x y => by rw [map_add]; rfl
    map_smul' := fun c x => by rw [map_smul]; rfl }

theorem dDecode_is_literal {f : ℤ[X]} (p : ℕ) (t : Site V) (probes : Probes V f)
    (samples : Fin (probeCount V)→Box f 1 p) (j : Fin (dOrder V t)) :
    dDecode V p t probes samples j =
      (J6ActiveNormalizer.quotientJet (dOrder V t) (dNormal V f p t)
        (J6ActiveInterpolation.decoded (dNode V p t probes) samples)).coeff j.val := rfl

theorem dDecode_true_quotient {f : ℤ[X]} (p : ℕ) (t : Site V) (probes : Probes V f)
    (hp : 0<p)
    (hf : f.Monic) (hF : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (F : (IntRing f 1)[X])
    (hdeg : F.natDegree≤J9PrintedSchedule.degreeBound (wireSize V) (2^rootA V))
    (j : Fin (dOrder V t)) :
    dDecode V p t probes (fun z => (F.map (reduce p f 1)).eval (dNode V p t probes z)) j =
      reduce p f 1 ((exactQuotient f 1 (rootA V) (wireSize V) (rootU V) t.val F).coeff j.val) := by
  have hd : (F.map (reduce p f 1)).natDegree ≤
      J9PrintedSchedule.degreeBound (wireSize V) (2^rootA V) :=
    Polynomial.natDegree_map_le.trans hdeg
  have he : J6ActiveInterpolation.decoded (dNode V p t probes)
      (fun z : Fin (probeCount V) => (F.map (reduce p f 1)).eval (dNode V p t probes z)) =
      F.map (reduce p f 1) :=
    J6ActiveInterpolation.decoded_exact (dNode V p t probes) (F.map (reduce p f 1)) hd
      (d_node_separation V p hp t probes hf hF)
  rw [dDecode_is_literal,he]
  unfold exactQuotient dNormal dOrder
  rw [← J6ActiveNormalizer.quotientJet_map, Polynomial.coeff_map]

def dPublicWeightAt {f : ℤ[X]} (p : ℕ) (t : Site V) (probes : Probes V f) (hf : f.Monic)
    (z : Fin (probeCount V)) : RatRing f 1 :=
  Paper5.D1Literal.publicWeight (dDecode V p t probes)
    (canonicalLift p f hf 1) (embed f 1) (dQuotientWeight V f t) z

theorem d_probe_multiplier_loss_at {f : ℤ[X]} (p : ℕ) (t : Site V)
    (hu : 0<rootU V) (hM : rootU V≤wireSize V)
    (probes : Probes V f) (hf : f.Monic) (z : Fin (probeCount V)) :
    HasLoss f 1 (ordinaryDLoss t) (dPublicWeightAt V p t probes hf z) := by
  classical
  choose w hw using fun j => d_quotient_weight_loss V f t hu hM j
  refine ⟨∑ j, w j * canonicalLift p f hf 1
    (dDecode V p t probes (Paper5.D1Literal.probeBasis z) j),?_⟩
  change (2:RatRing f 1)^ordinaryDLoss t *
    (∑ j, dQuotientWeight V f t j *
      embed f 1 (canonicalLift p f hf 1 (dDecode V p t probes (Paper5.D1Literal.probeBasis z) j))) =
    embed f 1 (∑ j, w j * canonicalLift p f hf 1 (dDecode V p t probes (Paper5.D1Literal.probeBasis z) j))
  rw [Finset.mul_sum,map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [← mul_assoc,hw j,map_mul])

def dPublicWeight {f : ℤ[X]} (t : Site V) (probes : Probes V f) (hf : f.Monic)
    (z : Fin (probeCount V)) : RatRing f 1 :=
  dPublicWeightAt V (high t) t probes hf z

theorem actual_D_probe_multiplier_loss {f : ℤ[X]} (t : Site V)
    (hu : 0<rootU V) (hM : rootU V≤wireSize V)
    (probes : Probes V f) (hf : f.Monic) (z : Fin (probeCount V)) :
    HasLoss f 1 (ordinaryDLoss t) (dPublicWeight V t probes hf z) :=
  d_probe_multiplier_loss_at V (high t) t hu hM probes hf z
#print axioms dDecode_is_literal
#print axioms dDecode_true_quotient
#print axioms actual_D_probe_multiplier_loss
end
end V8NativeMessage.C3.Hermite.D