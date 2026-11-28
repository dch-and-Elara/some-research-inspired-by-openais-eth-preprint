import J6R75OuterTimeSlotData
import J6R34OfficialGatewayCore

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 14000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Obtain the typed group operand from the actually emitted request row.
The extra reconstruction of its exterior descriptor is billed explicitly;
the original submit already owns its distinct installation descriptor.
Transport along row identity erases, without computing a canonical row. -/
namespace J6R75OuterTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath J6R35GatewayPreparation
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R66.BootPeak
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R19Retained AOracleMachineTimeTape A1R10 A1R12
open J6R34OfficialGateway J6R33OriginalJ6 J6R68AbsolutePrescribed
open J6R63Active J6R62ActivePrep J6R14ZeroMode

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
local notation "Centre" => (J6Recovery.Addr m)
local notation "Sample" => (Fin (literalDegree m native+1))

variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable (R : RawGroupPlans D S pad prior cfg rate cw)
variable (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)

def paidOnWrittenRow (r : Entry D.mark m native tc tj tw) (written : r∈S.requests.rows)
    (A : RawGroupPlan D S pad prior r cfg rate cw) :
    Meter (Block (frameOfPlan D S pad prior r A) ell) :=
  let physical := entrySource (W:=W) D r
  let continuation := runAdmittedRaw D S pad prior r sync reserved written physical.result rfl
    A.machine A.keep A.chart A.layout A.retire
  ⟨continuation.result.1,physical.steps+continuation.steps+3⟩

/-- Transport only the dependent value type. Runtime dispatch and its
debit use the actual generated row, not the representative in the proof. -/
def transportPaid {I : Type} (F : I→Type) {i j : I} (h : i=j)
    (out : Meter (F i)) : Meter (F j) := ⟨h ▸ out.result,out.steps⟩

abbrev sameRowFamily (i : Centre) (j : Sample) (g : Fin 64)
    (u : {r : Entry D.mark m native tc tj tw // r=sourceRow (W:=W) D i j g}) :
    Type :=
  Block (frameOfPlan D S pad prior u.val (u.property.symm ▸ R i j g)) ell

def paidSourceGroup (i : Centre) (j : Sample) (g : Fin 64)
    (H : ExactHead m native tc tj tw i j) (same : H=(prepareHead W i j).result) :
    Meter (Block (actualGroupFrame D S pad prior R i j g) ell) :=
  let addressed := emitEntry D.mark (i,j) H g
  have eq : addressed.result=sourceRow (W:=W) D i j g := by
    subst H
    rfl
  let u : {r : Entry D.mark m native tc tj tw // r=sourceRow (W:=W) D i j g} :=
    ⟨addressed.result,eq⟩
  let v : {r : Entry D.mark m native tc tj tw // r=sourceRow (W:=W) D i j g} :=
    ⟨sourceRow (W:=W) D i j g,rfl⟩
  have seen : u.val∈S.requests.rows := by
    change addressed.result∈S.requests.rows
    rw [eq]
    exact canonical_source_row_is_resident D S i j g
  let rowPlan : RawGroupPlan D S pad prior u.val cfg rate cw := u.property.symm ▸ R i j g
  let localRun : Meter (sameRowFamily D S pad prior R i j g u) :=
    paidOnWrittenRow D S pad prior sync reserved u.val seen rowPlan
  let delivered := transportPaid (sameRowFamily D S pad prior R i j g) (show u=v from Subtype.ext eq) localRun
  ⟨delivered.result,addressed.steps+delivered.steps+3⟩

def coreRawGroup (i : Centre) (j : Sample) (g : Fin 64) :
    Meter (Block (actualGroupFrame D S pad prior R i j g) ell×
      PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) :=
  let row := sourceRow (W:=W) D i j g
  let X := actualExterior (W:=W) D row
  let plan := R i j g
  runRawPhysicalExterior X plan.machine plan.keep plan.chart plan.layout plan.retire
    (publishedBank D S pad prior row) (published_head_is_the_actual_raw_header D S pad prior row)

theorem raw_group_is_the_real_metered_contraction
    (i : Centre) (j : Sample) (g : Fin 64)
    (H : ExactHead m native tc tj tw i j) (same : H=(prepareHead W i j).result) :
    let addressed := emitEntry D.mark (i,j) H g
    let group := paidSourceGroup D S pad prior R sync reserved i j g H same
    let core := coreRawGroup D S pad prior R i j g
    group.result=core.result.1 ∧
    group.steps=addressed.steps+(entrySource (W:=W) D addressed.result).steps+
      (submitResidentRow D S pad prior addressed.result).steps+core.steps+10 := by
  subst H
  let e := emitEntry D.mark (i,j) (prepareHead W i j).result g
  let row := sourceRow (W:=W) D i j g
  let source := entrySource (W:=W) D row
  let A := R i j g
  let out := runAdmittedRaw D S pad prior row sync reserved
    (canonical_source_row_is_resident D S i j g) source.result rfl A.machine A.keep A.chart A.layout A.retire
  let core := coreRawGroup D S pad prior R i j g
  have q : out=⟨core.result,(submitResidentRow D S pad prior row).steps+core.steps+4⟩ :=
    publication_then_raw_is_one_actual_meter D S pad prior row sync reserved
      (canonical_source_row_is_resident D S i j g) source.result rfl A.machine A.keep A.chart A.layout A.retire
  change out.result.1=core.result.1 ∧
    e.steps+(source.steps+out.steps+3)+3=
      e.steps+source.steps+(submitResidentRow D S pad prior row).steps+core.steps+10
  refine ⟨congrArg (fun x=>x.result.1) q,?_⟩
  have fee : out.steps=(submitResidentRow D S pad prior row).steps+core.steps+4 :=
    congrArg Meter.steps q
  rw [fee]
  omega

def verifiedSourceGroup (i : Centre) (j : Sample) (g : Fin 64)
    (H : ExactHead m native tc tj tw i j) (same : H=(prepareHead W i j).result) :
    GroupReceipt (ell:=ell) G D.hf i j g where
  frame := actualGroupFrame D S pad prior R i j g
  run := paidSourceGroup D S pad prior R sync reserved i j g H same
  truth := by
    let row := sourceRow (W:=W) D i j g
    let A := R i j g
    have correct := actual_raw_contraction_and_occurrence_bill A.machine A.keep A.chart
      (physicalExteriorInputs (actualExterior (W:=W) D row) A.layout) A.retire
      (publishedBank D S pad prior row) (published_head_is_the_actual_raw_header D S pad prior row)
      A.valid A.leaves A.entrance.depth
    rw [(raw_group_is_the_real_metered_contraction D S pad prior R sync reserved i j g H same).1]
    exact correct.1

#print axioms paidOnWrittenRow
#print axioms transportPaid
#print axioms paidSourceGroup
#print axioms raw_group_is_the_real_metered_contraction
#print axioms verifiedSourceGroup
end
end J6R75OuterTime

