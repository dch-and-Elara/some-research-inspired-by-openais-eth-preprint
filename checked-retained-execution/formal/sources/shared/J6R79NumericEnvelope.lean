import J6R79NumericScope
import J6R68ActiveInputsSweepPhysical

/-! Instantiate the R68 numeric gate from separate paid source producers
and actual finite dimensions. In particular the exponent is chosen
before any measured complete phase cost is observed. -/
namespace J6R79Numeric
open scoped Polynomial
open Polynomial J6R21Leaf J6R57LeafCap J6R55CachedLedger J6R57ActiveFee J6R65LeafRate
open J6R24MeteredRecursion J6ActiveRun J6R11Blueprint J6R12Blueprint J6R10Reachable
open J1PPrinted J6R50SourceProducer J6R51Online J6R67UnifiedRate
open J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R16ModeCost
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 22000000
set_option maxRecDepth 4300

theorem printedLeaf_le_input (s : ℕ) :
    J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) ≤ s := by
  unfold J9PrintedSchedule.leafThreshold
  set d := (Nat.clog 2 s).sqrt
  by_cases hd : d=0
  · simp [hd]
  · apply Nat.lt_succ_iff.mp
    apply (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hd)).2
    rw [Nat.succ_mul]
    have hs : s≤s*d := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hd)
    omega

def terminalArithRoof (K : ℕ) :=
  leafArithmeticScale (4*K) K (K+160*K^3) K (K+4*K^2) 0

theorem sourceArithmetic_le_actual_dimensions {f : ℤ[X]} {ell s C K : ℕ}
    (r : Call (PhysicalHost f ell)) (S : s≤K) (CC : C≤K) (L : Nat.clog 2 s≤K)
    (width : ell≤K) (precision : r.prec≤K) (vertices : vertexCount r.host≤K) :
    sourceArithmetic s C r ≤ terminalArithRoof K := by
  have he : 4*Nat.clog 2 s≤4*K := Nat.mul_le_mul_left _ L
  have hp : r.prec+160*C*s^2≤K+160*K^3 := by
    have hcs : C*s^2≤K^3 := by
      rw [pow_succ' K 2]
      exact Nat.mul_le_mul CC (Nat.pow_le_pow_left S 2)
    have hmul := Nat.mul_le_mul_left 160 hcs
    simpa only [Nat.mul_assoc] using Nat.add_le_add precision hmul
  have hv : vertexCount r.host+4*(C*s)≤K+4*K^2 := by
    rw [pow_two]
    exact Nat.add_le_add vertices (Nat.mul_le_mul_left _ (Nat.mul_le_mul CC S))
  have hH := (printedLeaf_le_input s).trans S
  unfold sourceArithmetic terminalArithRoof leafArithmeticScale dimEnvelope
  gcongr

/-- This term is the stock active cost at zero supplier debit;
actual paid selected-layout ingress is added separately. -/
def structuralActive (K : ℕ) := sweptActivePx K (selectedLayoutRoof K+3)

theorem activePx_exact_split (K ingress : ℕ) :
    sweptActivePx K (ingress+selectedLayoutRoof K+3)=ingress+structuralActive K := by
  simp only [structuralActive, sweptActivePx, sweptSetupPx, activeNodeFixedPrice]
  ring

structure ProducerCoefficients where
  selectedLayout : ℕ
  positiveOwner : ℕ
  boot : ℕ
  demand : ℕ
  queries : ℕ
  sourceWords : ℕ
  prep : ℕ
  reader : ℕ

/-- These are separate observed producers, not a cap on their aggregate
and not a premise on the final recurse. The reader coefficient already
has its native R65 exponent; preparation is not charged a second time. -/
structure IndividualProducerBounds
    (A : ProducerCoefficients) (H p ingress provider boot demand queries words prep reader : ℕ) :
    Prop where
  ingressCap : ingress≤A.selectedLayout*2^(p*H)
  ownerCap : provider≤A.positiveOwner*2^(p*H)
  bootCap : boot≤A.boot*2^(p*H)
  demandCap : demand≤A.demand*2^(p*H)
  queryCap : queries≤A.queries*2^(p*H)
  wordsCap : words≤A.sourceWords*2^(p*H)
  prepCap : prep≤A.prep
  readerCap : reader≤A.reader

def printedLocalExponent (producerPower leafPower : ℕ) :=
  max producerPower (leafPower+1)

def sourceCoefficient (K : ℕ) (A : ProducerCoefficients) :=
  (A.positiveOwner+A.prep+A.reader+terminalArithRoof K)+
  (A.selectedLayout+structuralActive K)+
  physicalAddressUnit K+
  (A.boot+A.demand+A.queries+A.sourceWords+structuralScope K)

private theorem growFactor (a H : ℕ) {u v : ℕ} (h : u≤v) :
    a*2^(u*H) ≤ a*2^(v*H) :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ h))

private theorem multiplyByFactor (a H v : ℕ) : a≤a*2^(v*H) :=
  Nat.le_mul_of_pos_right _ (by positivity)

theorem measured_local_numeric_from_individual_producers
    {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
    {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
    {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
    {M : OnlineMachine T key prec tw bw page q} {B : PageBank f ell key prec tw bw page}
    (F : MeasuredScopeInputs M B) (K ptr : ℕ)
    (G : ScopeSizes s C r.edges key prec tw bw page ptr B.headers.length B.records.length
      F.wordCaps F.atlasSize K)
    (S : s≤K) (CC : C≤K) (outer : ell≤K) (precision : r.prec≤K) (vertices : vertexCount r.host≤K)
    (ingress provider prep reader producerPower leafPower : ℕ) (A : ProducerCoefficients)
    (caps : IndividualProducerBounds A (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))
      producerPower ingress provider F.bootBudget F.demandBudget F.queryBudget F.sourceWordBudget prep reader) :
    let H := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)
    max (provider+(prep+reader+sourceArithmetic s C r)*2^((leafPower+1)*H))
        (sweptActivePx K (ingress+selectedLayoutRoof K+3))+
      (physicalAddressUnit K+measuredPerScope F ptr) ≤
      sourceCoefficient K A*2^(printedLocalExponent producerPower leafPower*H) := by
  let H := J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)
  let L := printedLocalExponent producerPower leafPower
  let E : ℕ := 2^(L*H)
  have liftProducer (a : ℕ) : a*2^(producerPower*H)≤a*E :=
    growFactor a H (le_max_left producerPower (leafPower+1))
  have liftLeaf (a : ℕ) : a*2^((leafPower+1)*H)≤a*E :=
    growFactor a H (le_max_right producerPower (leafPower+1))
  have liftFixed (a : ℕ) : a≤a*E := multiplyByFactor a H L
  have hA := sourceArithmetic_le_actual_dimensions r S CC G.lambda outer precision vertices
  have hPrep : prep+reader+sourceArithmetic s C r≤A.prep+A.reader+terminalArithRoof K :=
    Nat.add_le_add (Nat.add_le_add caps.prepCap caps.readerCap) hA
  have hLeaf : provider+(prep+reader+sourceArithmetic s C r)*2^((leafPower+1)*H) ≤
        (A.positiveOwner+A.prep+A.reader+terminalArithRoof K)*E := by
    have hOwner := caps.ownerCap.trans (liftProducer _)
    have hWord := (Nat.mul_le_mul_right (2^((leafPower+1)*H)) hPrep).trans (liftLeaf _)
    calc
      _ ≤ A.positiveOwner*E+(A.prep+A.reader+terminalArithRoof K)*E :=
        Nat.add_le_add hOwner hWord
      _ = _ := by ring
  have hActive : sweptActivePx K (ingress+selectedLayoutRoof K+3)≤
      (A.selectedLayout+structuralActive K)*E := by
    rw [activePx_exact_split,Nat.add_mul]
    exact Nat.add_le_add (caps.ingressCap.trans (liftProducer _)) (liftFixed _)
  have hScope : measuredPerScope F ptr≤
      (A.boot+A.demand+A.queries+A.sourceWords+structuralScope K)*E := by
    have first := derivedScope_le_producers_add_structural G F.bootBudget F.demandBudget
      F.queryBudget F.sourceWordBudget
    change measuredPerScope F ptr≤_ at first
    refine first.trans ?_
    simp only [Nat.add_mul]
    exact Nat.add_le_add
      (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (caps.bootCap.trans (liftProducer _))
        (caps.demandCap.trans (liftProducer _))) (caps.queryCap.trans (liftProducer _)))
        (caps.wordsCap.trans (liftProducer _))) (liftFixed _)
  change max (provider+(prep+reader+sourceArithmetic s C r)*2^((leafPower+1)*H))
      (sweptActivePx K (ingress+selectedLayoutRoof K+3))+
      (physicalAddressUnit K+measuredPerScope F ptr)≤sourceCoefficient K A*E
  have hArith := liftFixed (physicalAddressUnit K)
  have hMax := max_le
    (hLeaf.trans (Nat.le_add_right _ ((A.selectedLayout+structuralActive K)*E)))
    (hActive.trans (Nat.le_add_left _ ((A.positiveOwner+A.prep+A.reader+terminalArithRoof K)*E)))
  refine (Nat.add_le_add hMax (Nat.add_le_add hArith hScope)).trans ?_
  unfold sourceCoefficient
  exact le_of_eq (by ring)

#print axioms printedLeaf_le_input
#print axioms sourceArithmetic_le_actual_dimensions
#print axioms activePx_exact_split
#print axioms measured_local_numeric_from_individual_producers
end J6R79Numeric
