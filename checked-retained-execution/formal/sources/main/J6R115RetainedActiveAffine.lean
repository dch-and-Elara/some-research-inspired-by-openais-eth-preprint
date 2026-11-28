import J6R115RetainedOccurrenceTariff
import J6R57ActiveFeeAffine

/-! The tariff is attached directly to the current retained execution,
including its own label/header pass and its own recursive calls. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack J6ActiveSchedule
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable J6R49Leaf J6R57Public J6R49Cost

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 26000000
set_option maxRecDepth 5300
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : KeptDrivers X M rank)
variable (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad)→ℕ)
variable (x : KeptInvocation X M)

open J6R114RetainedScopeTariff J6R55CachedLedger J6R57ActiveFee J6R16ModeCost

variable (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))

theorem actual_retained_active_own_tariff_is_affine_in_its_real_addresses
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges)
    (fixed arithmetic scope scan : ℕ)
    (prefixCap : let p := Path.step x.path x.slot
      let H := readGroupHeadersForActive X x.path x.slot x.site x.entry
      let W := D.layout x on H.result
      let L := selectedLayoutAndLabels W.setup
      let A := prepareFromKeptLayout X x.path x.slot x.site x.entry M on L.result
        (D.fit p on) D.masks L.steps
      H.steps+(mountResident x.site x.entry.resident).steps+A.steps+
        fixedActive A.result.proofView (reachable_positive T p.reached) T.vPositive≤fixed)
    (unit : let p := Path.step x.path x.slot
      let H := readGroupHeadersForActive X x.path x.slot x.site x.entry
      let W := D.layout x on H.result
      let L := selectedLayoutAndLabels W.setup
      let A := prepareFromKeptLayout X x.path x.slot x.site x.entry M on L.result
        (D.fit p on) D.masks L.steps
      ∀ t∈A.result.proofView.centres,
        unitMode (A.result.proofView.tape t).low (A.result.proofView.tape t).tape.result≤64*arithmetic)
    (perScope : ∀ u : (Plan sel).Slot x.call,
      cachedScopeOwn M retire initial (.step x.path x.slot) u≤scope)
    (scanOnce : keptSuccessorOwnerScan X x.path x.slot x.site x.entry
      (readGroupHeadersForActive X x.path x.slot x.site x.entry).result≤scan) :
    retainedOwnTariff X M D retire x initial≤
      fixed+(arithmetic+scope+scan)*Nat.card ((Plan sel).Slot x.call) := by
  classical
  let p := Path.step x.path x.slot
  let H := readGroupHeadersForActive X x.path x.slot x.site x.entry
  let W := D.layout x on H.result
  let L := selectedLayoutAndLabels W.setup
  let A := prepareFromKeptLayout X x.path x.slot x.site x.entry M on L.result
    (D.fit p on) D.masks L.steps
  let hp := reachable_positive T p.reached
  let overhead := H.steps+(mountResident x.site x.entry.resident).steps+A.steps
  have ops := active_arithmetic_charged_against_actual_slots A.result.proofView hp T.vPositive arithmetic unit
  have base := Nat.add_le_add_left ops overhead
  rw [←Nat.add_assoc] at base
  have fixedBound := base.trans (Nat.add_le_add_right prefixCap _)
  letI : Fintype ((Plan sel).Slot x.call) := (Plan sel).finiteSlot x.call
  let scanSteps := keptSuccessorOwnerScan X x.path x.slot x.site x.entry H.result
  have visits : (∑ u : (Plan sel).Slot x.call, (cachedScopeOwn M retire initial p u+scanSteps))≤
      (scope+scan)*Nat.card ((Plan sel).Slot x.call) := by
    calc
      _≤∑ _ : (Plan sel).Slot x.call, (scope+scan) :=
        Finset.sum_le_sum (fun u _=>Nat.add_le_add (perScope u) scanOnce)
      _=_ := by
        rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.card_eq_fintype_card,Nat.mul_comm]
        rfl
  rw [retainedOwnTariff,dif_pos on]
  exact (Nat.add_le_add fixedBound visits).trans (le_of_eq (by ring))

#print axioms actual_retained_active_own_tariff_is_affine_in_its_real_addresses
end
end J6R111KeptOwnerFlow

