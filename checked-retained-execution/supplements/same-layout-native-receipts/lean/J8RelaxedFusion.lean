import J8RelaxedAllPins
import J8RelaxedBase
import J9R13PhysicalFusion
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace J8Physical.Relaxed
open scoped Classical BigOperators Polynomial
open Polynomial LiteralPortCompiler J8EndToEnd J8J9Grouped
open J9R13Compiler J9R13GroupFusion J9R13PhysicalTables J9LayoutTransfer J9R13PhysicalFusion
open DyadicProbeCompiler NativeProbeRing
noncomputable section
local instance (priority := 10000) literalFinDecEq (n : ℕ) : DecidableEq (Fin n) :=
  fun i j => Classical.propDecidable (i=j)
variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
def groupedSource (e : RowEndpointSeating d) (even : Even L) (a : S)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) : Source[X] :=
  liftedGroup d F (physicalBase d e even (J9FactorBounds.kernel L) tail)
    sign (d.pinLabel a) none (integralFeature d a b)

def groupedTarget (e : RowEndpointSeating d) (even : Even L) (a : S)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (j : TargetPorts d a) : Source[X] :=
  liftedGroup d F (physicalBase d e even (J9FactorBounds.kernel L) tail)
    sign (d.rowLabel (pinWire d a).1) (some j) (fun _ => 1)

def groupedPublic (e : RowEndpointSeating d) (even : Even L) (a : S)
    (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d) : Source[X] :=
  liftedPublic d a F (physicalBase d e even (J9FactorBounds.kernel L) tail) sign

def highObservation (e : RowEndpointSeating d) (even : Even L) (hL : 2 < L)
    (a : S) (F : OldTables d) (sign : S → Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a → Source[X])
    (k q : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree → Bool) : Scalar q f :=
  groupedProbe q f (k+1+(b:ℕ)) (groupedTargets d a) (groupedPublic d e even a F sign tail)
    (groupedSource d e even a F sign tail b) (groupedTarget d e even a F sign tail)
    (physicalKernel d a even hL (J9FactorBounds.kernel L) b kt) (probe q f addr)

omit [Fintype Packet] in
theorem native_matches_physicalCoeff (e : RowEndpointSeating d) (even : Even L) (hL : 2 < L)
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

def baseline (e : RowEndpointSeating d) (even : Even L) (idx : Wire R ≃ Fin M)
    (tail : IntegralArguments d) (x : Fin M→Bool) (p : Port R) : Source[X] :=
  baseAt d.rowLabel (physicalBase d e even (J9FactorBounds.kernel L) tail)
    ((cubeEquiv d idx).symm x) p

def literalBase (e : RowEndpointSeating d) (even : Even L) (a : S) (idx : Wire R ≃ Fin M)
    (tail : IntegralArguments d) (b : Fin (Fintype.card (PinTile d a))) :
    (Site M R→Bool)→Site M R→Source[X] :=
  base (baseline d e even idx tail) (featureValue d a idx b)

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 4500000 in
theorem physical_compiler_singleton (e : RowEndpointSeating d) (even : Even L) (hL : 2 < L)
    (a : S) (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a)
    (idx : Wire R ≃ Fin M) (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a→Source[X]) :
    MvPolynomial.coeff β (completed (literalSystem d idx F sign)
      (literalBase d e even a idx tail b) (literalKernel d (M:=M) even hL a b kt)) =
      groupedNormalized (groupedTargets d a) (groupedPublic d e even a F sign tail)
        (groupedSource d e even a F sign tail b) (groupedTarget d e even a F sign tail)
        (physicalKernel d a even hL (J9FactorBounds.kernel L) b kt) := by
  let u := physicalBase d e even (J9FactorBounds.kernel L) tail
  let gs := d.pinLabel a
  let gt := d.rowLabel (pinWire d a).1
  let κ := physicalKernel d a even hL (J9FactorBounds.kernel L) b kt
  have H := grouped_completed (globalCNF d idx F sign) (cubeEquiv d idx) d.rowLabel u
    (weight d F sign) (weight_global d idx F sign) gs gt off.symm
    (fun x => Polynomial.C (integralFeature d a b x)) (groupedTargets d a) id κ
  change MvPolynomial.coeff β (completed (literalSystem d idx F sign)
    (literalBase d e even a idx tail b) (literalKernel d (M:=M) even hL a b kt)) = _ at H
  rw [H]
  unfold groupedNormalized groupedPublic groupedSource groupedTarget
  change ((baselinePub d.rowLabel u (weight d F sign) gs gt) *
     childSum d.rowLabel u (weight d F sign) gs none (fun x => Polynomial.C (integralFeature d a b x))) *
      ∑ j ∈ groupedTargets d a, κ j * childSum d.rowLabel u (weight d F sign) gt (some j) (fun _ => 1) =
    (liftedPublic d a F u sign * liftedGroup d F u sign gs none (integralFeature d a b)) *
      ∑ j ∈ groupedTargets d a, κ j * liftedGroup d F u sign gt (some j) (fun _ => 1)
  rw [public_lifted,childSum_lifted]
  have eq (j : TargetPorts d a) :
      childSum d.rowLabel u (weight d F sign) gt (some j) (fun _ => 1) =
        liftedGroup d F u sign gt (some j) (fun _ => 1) := by
    simpa only [map_one] using childSum_lifted d F u sign gt (some j) (fun _ => 1)
  simp only [eq]

set_option linter.unusedSectionVars false in
theorem observation_is_physical_child_product (e : RowEndpointSeating d) (even : Even L) (hL : 2 < L)
    (a : S) (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a)
    (idx : Wire R ≃ Fin M) (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a→Source[X])
    (k q : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree→Bool) :
    J9End.observation q f addr (literalSystem d idx F sign)
      (literalBase d e even a idx tail b) (literalKernel d (M:=M) even hL a b kt)
      (fun _ => k+1+(b:ℕ)) () =
      highObservation d e even hL a F sign tail b kt k q f addr := by
  rw [observation_eval,physical_compiler_singleton d e even hL a off]
  exact (groupedProbe_eval q f _ _ _ _ _ _ _).symm

set_option linter.unusedSectionVars false in
theorem physical_first_derived (e : RowEndpointSeating d) (even : Even L) (hL : 2 < L)
    (a : S) (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a)
    (idx : Wire R ≃ Fin M) (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (higher : RestArguments d) (b : Fin (Fintype.card (PinTile d a)))
    (kt : TargetPorts d a→Source[X]) (rest : TargetPorts d a→ℚ[X])
    (k : ℕ) (length : L=2^k) :
    (2:ℚ)^(k+1+(b:ℕ)) * rationalMap
      ((MvPolynomial.coeff β (completed (literalSystem d idx F sign)
        (literalBase d e even a idx tail b) (literalKernel d (M:=M) even hL a b kt))).coeff 0) =
      physicalCoeff d e even a F sign higher b rest := by
  rw [physical_compiler_singleton d e even hL a off]
  exact native_matches_physicalCoeff d e even hL k length a F sign tail higher b kt rest

#print axioms physical_compiler_singleton
#print axioms observation_is_physical_child_product
#print axioms physical_first_derived
end
end J8Physical.Relaxed