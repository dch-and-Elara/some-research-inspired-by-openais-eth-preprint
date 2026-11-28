import J9R13GroupFusion
import J9R13PhysicalTables
import J8J9GroupedReadout

/-!
# The physical grouped sample is literally a J9 observation

Here the source and target data are the actual seated J8 child systems.
The two-port row truth, rigid pin addresses and old column clauses are
not assumed equal to an external aggregate coefficient. The entire
odd-localized singleton polynomial agrees, for arbitrary honest row and
crossing tails. Consequently every finite observation agrees.
-/

namespace J9R13PhysicalFusion
open scoped Classical BigOperators Polynomial
open LiteralPortCompiler J8Physical J8EndToEnd J8J9Grouped
open J9R13Compiler J9R13GroupFusion J9R13PhysicalTables J9LayoutTransfer
open DyadicProbeCompiler NativeProbeRing

noncomputable section
-- Match the generic compiler's proof-time equality choice on its left cube.
local instance (priority := 10000) literalFinDecEq (n : ℕ) : DecidableEq (Fin n) :=
  fun i j => Classical.propDecidable (i=j)

variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

def weight (F : OldTables d) (sign : S→Bool) (g : G) (x : Assignment d g) : Source[X] :=
  Polynomial.C (pinWeightSource (fun i : LocalPin d g => sign i.1) x.1 *
    physicalTableWeight d F g x.2)

set_option linter.unusedSectionVars false in
theorem weight_global (idx : Wire R ≃ Fin M) (F : OldTables d) (sign : S→Bool) (x : J8J9Grouped.Cube d) :
    (truth (globalCNF d idx F sign) (cubeEquiv d idx x) : Source[X]) =
      ∏ g : G, weight d F sign g (x g) := by
  have H := congrArg (Polynomial.C (R:=Source)) (global_truth d (K:=Source) idx F sign x)
  simpa only [map_truth,map_prod,weight,pinWeightSource,physicalTableWeight] using H

set_option linter.unusedSectionVars false in
theorem childSum_lifted (F : OldTables d) (u : IntegralArguments d) (sign : S→Bool)
    (g : G) (mark : Option (LocalRow d g×Bool)) (feat : Assignment d g→Source) :
    childSum d.rowLabel u (weight d F sign) g mark (fun x => Polynomial.C (feat x)) =
      liftedGroup d F u sign g mark feat := by
  unfold childSum liftedGroup integralChild
  change (∑ x : (LocalPin d g→Bool)×LocalBits d g, _) = _
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro p _
  simp only [childAt,weight,map_mul]
  ring

set_option linter.unusedSectionVars false in
theorem public_lifted (F : OldTables d) (u : IntegralArguments d) (sign : S→Bool) (a : S) :
    baselinePub d.rowLabel u (weight d F sign) (d.pinLabel a) (d.rowLabel (pinWire d a).1) =
      liftedPublic d a F u sign := by
  unfold baselinePub liftedPublic
  apply Finset.prod_congr rfl
  intro g _
  have h := childSum_lifted d F u sign g none (fun _ => 1)
  simpa only [map_one] using h

/-- Whole physical baseline: the row pair is read from its true owner. -/
def baseline (e : EndpointSeating d) (even : Even L) (idx : Wire R ≃ Fin M)
    (tail : IntegralArguments d) (x : Fin M→Bool) (p : Port R) : Source[X] :=
  baseAt d.rowLabel (physicalBase d e even (J9FactorBounds.kernel L) tail)
    ((cubeEquiv d idx).symm x) p

def featureValue (a : S) (idx : Wire R ≃ Fin M) (b : Fin (Fintype.card (PinTile d a)))
    (x : Fin M→Bool) : Source[X] :=
  Polynomial.C (integralFeature d a b (((cubeEquiv d idx).symm x) (d.pinLabel a)))

def crossing (even : Even L) (hL : 2 < L) (a : S) (b : Fin (Fintype.card (PinTile d a)))
    (kt : TargetPorts d a→Source[X]) (p : Port R) : Source[X] :=
  targetKernel (groupedTargets d a) (fun j => (j.1.1,j.2))
    (physicalKernel d a even hL (J9FactorBounds.kernel L) b kt) p

abbrev Site (M : ℕ) (R : Type*) := J9R13Compiler.Site (Fin M) R

def literalSystem (idx : Wire R ≃ Fin M) (F : OldTables d) (sign : S→Bool) :
    CNF (Site M R) := system (R:=R) (globalCNF d idx F sign)

def literalBase (e : EndpointSeating d) (even : Even L) (a : S) (idx : Wire R ≃ Fin M)
    (tail : IntegralArguments d) (b : Fin (Fintype.card (PinTile d a))) :
    (Site M R→Bool)→Site M R→Source[X] :=
  base (baseline d e even idx tail) (featureValue d a idx b)

def literalKernel (even : Even L) (hL : 2 < L) (a : S) (b : Fin (Fintype.card (PinTile d a)))
    (kt : TargetPorts d a→Source[X]) : (Site M R→Bool)→Site M R→Unit→Source[X] :=
  kernel (fun _ p _ => crossing d even hL a b kt p)

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 4500000 in
theorem physical_compiler_singleton (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
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

/-- General formula for every point of a concrete singleton query. -/
theorem observation_eval {A : Type*} [Fintype A] [DecidableEq A]
    (p : ℕ) (f : ℤ[X]) (addr : Fin f.natDegree→Bool) (w : ℕ)
    (F : CNF A) (B : (A→Bool)→A→Source[X]) (K : (A→Bool)→A→Unit→Source[X]) :
    J9End.observation p f addr F B K (fun _ => w) () =
      (2:Scalar p f)^w * probe p f addr *
        (MvPolynomial.coeff β (completed F B K)).eval₂ (toScalar p f) (2*probe p f addr) := by
  unfold J9End.observation
  rw [DyadicSlotCompiler.p3_evaluated]
  simp [β,DyadicSlotCompiler.valuation,DyadicSlotCompiler.order]

theorem groupedProbe_eval {T : Type*} (p : ℕ) (f : ℤ[X]) (w : ℕ) (s : Finset T)
    (pub src : Source[X]) (target cross : T→Source[X]) (z : Scalar p f) :
    groupedProbe p f w s pub src target cross z =
      (2:Scalar p f)^w*z *
        (groupedNormalized s pub src target cross).eval₂ (toScalar p f) (2*z) := by
  let E := Polynomial.eval₂RingHom (toScalar p f) (2*z)
  change (E pub * E src) * (∑ j ∈ s, ((2:Scalar p f)^w*z*E (cross j))*E (target j)) =
    (2:Scalar p f)^w*z * E (groupedNormalized s pub src target cross)
  simp only [groupedNormalized,map_mul,map_sum,mul_assoc,← Finset.mul_sum]
  ring

set_option linter.unusedSectionVars false in
theorem observation_is_physical_child_product (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
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
theorem physical_first_derived (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
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

#print axioms weight_global
#print axioms childSum_lifted
#print axioms physical_compiler_singleton
#print axioms observation_is_physical_child_product
#print axioms physical_first_derived

end
end J9R13PhysicalFusion
