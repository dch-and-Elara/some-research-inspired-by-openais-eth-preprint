import J6R79NumericEnvelope

/-! A common R75 rate can only be raised from the actual individual
source debits. Different groups may allocate their charge differently
between stopped, active and scoped phases. The common R79 expression
below absorbs each actual component without choosing an exponent after
observing any complete group runtime. -/
namespace J6R102FinalPhase
open scoped Polynomial
open Polynomial J6R21Leaf J6R57LeafCap J6R55CachedLedger J6R57ActiveFee J6R65LeafRate
open J6R24MeteredRecursion J6ActiveRun J6R11Blueprint J6R12Blueprint J6R10Reachable
open J1PPrinted J6R50SourceProducer J6R51Online J6R67UnifiedRate
open J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R16ModeCost
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R79Numeric J6R56PrintedExponent
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4300
set_option maxHeartbeats 14500000

noncomputable section

def leafHeight (s : ℕ) : ℕ := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)

def localClock (s K producerPower leafPower : ℕ) (A : ProducerCoefficients) : ℕ :=
  sourceCoefficient K A*2^(printedLocalExponent producerPower leafPower*leafHeight s)

theorem three_uniform_debits_have_the_original_exponent (s K producerPower leafPower : ℕ)
    (A : ProducerCoefficients) :
    let L := localClock s K producerPower leafPower A
    L+(L+L) = (3*sourceCoefficient K A)*2^(printedLocalExponent producerPower leafPower*leafHeight s) := by
  unfold localClock
  dsimp only
  ring

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {M : OnlineMachine T key prec tw bw page q} {B : PageBank f ell key prec tw bw page}

theorem each_actual_budget_below_the_same_printed_clock
    (F : MeasuredScopeInputs M B) (K pointerWidth : ℕ)
    (size : ScopeSizes s C r.edges key prec tw bw page pointerWidth B.headers.length B.records.length
      F.wordCaps F.atlasSize K)
    (input : s ≤ K) (constant : C ≤ K) (truncation : ell ≤ K)
    (rx : r.prec ≤ K) (vertices : vertexCount r.host ≤ K)
    (ingress owner prep reader producerPower leafPower : ℕ) (A : ProducerCoefficients)
    (individual : IndividualProducerBounds A (leafHeight s) producerPower ingress owner
      F.bootBudget F.demandBudget F.queryBudget F.sourceWordBudget prep reader) :
    let L := localClock s K producerPower leafPower A
    let fixed := max (owner+(prep+reader+sourceArithmetic s C r)*2^((leafPower+1)*leafHeight s))
      (sweptActivePx K (ingress+selectedLayoutRoof K+3))
    fixed ≤ L ∧ physicalAddressUnit K ≤ L ∧ measuredPerScope F pointerWidth ≤ L := by
  let H := leafHeight s
  let L := localClock s K producerPower leafPower A
  let fixed := max (owner+(prep+reader+sourceArithmetic s C r)*2^((leafPower+1)*H))
    (sweptActivePx K (ingress+selectedLayoutRoof K+3))
  have bound : fixed+(physicalAddressUnit K+measuredPerScope F pointerWidth) ≤ L :=
    measured_local_numeric_from_individual_producers F K pointerWidth size input constant truncation rx vertices
      ingress owner prep reader producerPower leafPower A individual
  exact ⟨(Nat.le_add_right _ _).trans bound,
    ((Nat.le_add_right _ _).trans (Nat.le_add_left _ _)).trans bound,
    ((Nat.le_add_left _ _).trans (Nat.le_add_left _ _)).trans bound⟩

theorem widen_real_phase_caps_to_a_uniform_clock {retire : PageJob f ell key prec tw bw page→ℕ}
    {fixed arithmetic perScope L : ℕ}
    (actual : CachedThreePhaseCaps M retire B fixed arithmetic perScope)
    (F : fixed ≤ L) (A : arithmetic ≤ L) (S : perScope ≤ L) :
    CachedThreePhaseCaps M retire B L L L := by
  refine ⟨fun z off=>(actual.leaf z off).trans F,?_,fun z w=>(actual.scope z w).trans S⟩
  intro z on
  exact (actual.active z on).trans (Nat.add_le_add F (Nat.mul_le_mul_right _ A))

#print axioms three_uniform_debits_have_the_original_exponent
#print axioms each_actual_budget_below_the_same_printed_clock
#print axioms widen_real_phase_caps_to_a_uniform_clock
end
end J6R102FinalPhase

