import J8J9GroupedRange
import J9EndProbe

/- Changes in elaborating imported chart enumerations can flag theorem-scope instances. This affects only the unused-section-variable style linter. -/
set_option linter.unusedSectionVars false

/-! Fully composed grouped recovery from high-precision literal binary
probes using the derived denominator and magnitude. -/

namespace J8J9Grouped
open scoped BigOperators Polynomial Classical
open Polynomial NativeProbeRing DyadicProbeCompiler J8Physical J8EndToEnd

noncomputable section

theorem groupedProbe_reduce {I : Type*} (p q : ℕ) (hpq : p ≤ q) (f : ℤ[X])
    (e : ℕ) (s : Finset I) (pub src : Source[X]) (trg ker : I → Source[X])
    (addr : Fin f.natDegree → Bool) :
    reduceScalar p q hpq f (groupedProbe q f e s pub src trg ker (probe q f addr)) =
      groupedProbe p f e s pub src trg ker (probe p f addr) := by
  simp only [groupedProbe, map_mul, map_pow, map_ofNat, map_sum,
    Polynomial.hom_eval₂, J9End.reduce_toScalar, same_probe_at_higher_precision]

variable {Packet R S V G : Type*} {P : V → Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

def physicalCoeff (e : EndpointSeating d) (even : Even L) (a : S) (F : OldTables d)
    (sign : S → Bool) (higher : RestArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (rest : TargetPorts d a → ℚ[X]) : ℚ :=
  let gs := d.pinLabel a
  let gt := d.rowLabel (pinWire d a).1
  let src := localChild d e even gs (outerAmplitude L) (F gs)
  let tgt := localChild d e even gt (outerAmplitude L) (F gt)
  (J8SourceMoment.completedTile (publicSiblings d e even a F higher sign) src tgt
    (fun i => sign i.1) (fun i => sign i.1) (higher gs) (higher gt)
    (fun i => tilePinInSource d (pinEnumeration d a i)) (coordinates d a)
    (fun b => tileBackground d a b) (groupedTargets d a) (2*(L:ℚ))
    (physicalDenominator d a) rest b).coeff 1

def groupedSource (e : EndpointSeating d) (even : Even L) (a : S)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) : Source[X] :=
  liftedGroup d F (physicalBase d e even (J9FactorBounds.kernel L) tail)
    sign (d.pinLabel a) none (integralFeature d a b)

def groupedTarget (e : EndpointSeating d) (even : Even L) (a : S)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (j : TargetPorts d a) : Source[X] :=
  liftedGroup d F (physicalBase d e even (J9FactorBounds.kernel L) tail)
    sign (d.rowLabel (pinWire d a).1) (some j) (fun _ => 1)

def groupedPublic (e : EndpointSeating d) (even : Even L) (a : S)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d) : Source[X] :=
  liftedPublic d a F (physicalBase d e even (J9FactorBounds.kernel L) tail) sign

def highObservation (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
    (a : S) (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (k q : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree → Bool) : Scalar q f :=
  groupedProbe q f (k+1+(b:ℕ)) (groupedTargets d a) (groupedPublic d e even a F sign tail)
    (groupedSource d e even a F sign tail b) (groupedTarget d e even a F sign tail)
    (physicalKernel d a even hL (J9FactorBounds.kernel L) b kt) (probe q f addr)

omit [Fintype Packet] in
theorem native_matches_physicalCoeff (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
    (k : ℕ) (length : L = 2^k) (a : S) (F : OldTables d) (sign : S → Bool)
    (tail : IntegralArguments d) (higher : RestArguments d) (b : Fin (Fintype.card (PinTile d a)))
    (kt : TargetPorts d a → Source[X]) (rest : TargetPorts d a → ℚ[X]) :
    (2:ℚ)^(k+1+(b:ℕ)) * rationalMap
      ((groupedNormalized (groupedTargets d a) (groupedPublic d e even a F sign tail)
        (groupedSource d e even a F sign tail b) (groupedTarget d e even a F sign tail)
        (physicalKernel d a even hL (J9FactorBounds.kernel L) b kt)).coeff 0) =
      physicalCoeff d e even a F sign higher b rest := by
  unfold physicalCoeff J8SourceMoment.completedTile groupedPublic groupedSource groupedTarget
  dsimp only
  have hc := printed_amplitude_integral L (by omega) even
  have agree := constructed_base_agrees d e even _ hc F tail
  apply grouped_first_matches
  · exact liftedPublic_matches d e even a F _ sign higher agree
  · exact liftedGroup_matches d e even F _ sign higher agree _ none _ _ (feature_agreement d a b)
  · intro j hj
    exact liftedGroup_matches d e even F _ sign higher agree _ (some j) _ _ (fun _ => map_one _)
  · intro j hj
    rw [J8SourceMoment.outerKernel_first]
    exact constructed_kernel_scales d a even hL _ hc k length b kt j hj
  · intro j hj
    exact J8SourceMoment.outerKernel_zero _ _ _ _ _

theorem highObservation_readout (e : EndpointSeating d) (even : Even L) (hL : 3 ≤ L)
    (k : ℕ) (length : L = 2^k) (a : S)
    (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a) (idx : Wire R ≃ Fin M)
    (hM : L^3 ≤ M) (capacity : L * Fintype.card Packet ≤ 3*M)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d) (higher : RestArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (rest : TargetPorts d a → ℚ[X]) (q : ℕ) (hpq : 10*M ≤ q)
    (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree) [Fact (Irreducible (residuePoly f))]
    (addr : Fin (10*M+1) → Fin f.natDegree → Bool) (distinct : Function.Injective addr) :
    let p := 10*M
    let x := fun j => probe p f (addr j)
    let obs := fun j => reduceScalar p q hpq f (highObservation d e even (by omega) a F sign tail b kt
      k q f (addr j))
    readRational p f hf (clear d a b) (NativeInterpolation.decode x obs ⟨1,by
      have hm : 0 < M := (show 0 < L^3 by positivity).trans_le hM
      omega⟩) =
      physicalCoeff d e even a F sign higher b rest := by
  dsimp only
  have hL' : 2 < L := by omega
  have hp : 0 < 10*M := by
    have hpos : 0 < L^3 := by positivity
    omega
  unfold highObservation
  simp only [groupedProbe_reduce]
  rw [grouped_decode_binary _ hp f hf hd _ (by omega) addr distinct]
  have hclear := (clear_positive_odd d even hL' a b).1.ne'
  have hfit := exactNum_centered d e even a off idx F sign b hL hM capacity
  have hfit' : exactNum d e even a F sign b * 2 ∈
      Set.Ioc (-(↑((2:ℕ)^(10*M))) : ℤ) ↑((2:ℕ)^(10*M)) := by exact_mod_cast hfit
  exact (lift_observed_first _ hp f hf hd _ _ _ _ hclear hfit'
    (exactNum_native d e even hL' k length a F sign tail b kt)).trans
    (native_matches_physicalCoeff d e even hL' k length a F sign tail higher b kt rest)

#print axioms groupedProbe_reduce
#print axioms native_matches_physicalCoeff
#print axioms highObservation_readout
end
end J8J9Grouped
