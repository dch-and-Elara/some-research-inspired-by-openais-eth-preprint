import J6R75OuterTimeSlotData
import J6R75OuterTimeRequest
import J6R57PublicRequestBounds

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 14000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Exact R57 submit debits, including both real probe reads, for the
actual written catalogue. The install remains a real outer publication
charge, not a part of the recursive R68 core. -/
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
open J6R33OriginalJ6 J6R68AbsolutePrescribed
open J6R63Active J6R62ActivePrep J6R14ZeroMode J6R27OriginalGate

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

variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))

theorem resident_probe_input_has_the_original_tariff :
    S.requests.probes=(buildRootBitBank G ell).result := by
  let reference := buildRequestInputs D W
  have common : S.root=reference.result.root := S.exactRoot
  have recognized : reference.result.requests.probes=(buildRootBitBank G ell).result :=
    (single_actual_input_cache D W).1
  exact S.sameProbes.trans
    ((congrArg (fun a : ActualRootPreparation G ell q=>a.probes) common).trans
      (reference.result.sameProbes.symm.trans recognized))

theorem real_probe_read_has_printed_bound (j : Sample) :
    (S.requests.probes.read j).steps ≤ (literalDegree m native+1)*(f.natDegree+2) := by
  rw [resident_probe_input_has_the_original_tariff D S]
  exact ((build_root_probe_receipt G ell).2 j).2

def lookupOuterRoof (m n key : ℕ) : ℕ :=
  6*key+16+((m+1)*(literalDegree m n+1)*64)*(10*key+9)

theorem legal_outer_request_lookup_has_printed_bound (i : Centre) (j : Sample) (g : Fin 64) :
    let r := sourceRow (W:=W) D i j g
    (rawRequest D.mark r.wire S.requests.rows).steps ≤ lookupOuterRoof m native (KeyWidth kp tc tj) := by
  let r := sourceRow (W:=W) D i j g
  have wires := actual_entry_wires W D.mark ((i,j),g)
  change (rawRequest D.mark r.wire S.requests.rows).steps ≤ _
  rw [S.requests.ordered]
  exact (native_raw_request_hit W D.mark r.wire ((i,j),g) wires.2.1 wires.2.2.1 wires.2.2.2.1).2

theorem literal_submit_uses_both_probe_reads (i : Centre) (j : Sample) (g : Fin 64) :
    let r := sourceRow (W:=W) D i j g
    let read := S.requests.probes.read j
    let query := rawRequest D.mark r.wire S.requests.rows
    (submitResidentRow D S pad prior r).steps =
      2*read.steps+query.steps+(eqRawBits read.result.val read.result.val).steps+
      (entrySource (W:=W) D r).steps+((cachedExteriorJob D S pad r).install prior).steps+14 := by
  let r := sourceRow (W:=W) D i j g
  let read := S.requests.probes.read j
  have good : read.result.val=List.ofFn ((rootPreset G ell).word r.coord.1.2) := S.requests.probes.consistent j
  have adm := peeled_admission_charges_the_real_lookup_sample_and_install D S pad prior r
    (canonical_source_row_is_resident D S i j g) read.result.val good
  have sub := legal_submit_has_the_extra_client_read D S pad prior r read.result.val good
  let query := rawRequest D.mark r.wire S.requests.rows
  let test := eqRawBits read.result.val read.result.val
  let ext := entrySource (W:=W) D r
  let ins := (cachedExteriorJob D S pad r).install prior
  let A := admitRequest D S pad prior r.wire read.result.val
  change A.steps=query.steps+read.steps+test.steps+ext.steps+ins.steps+11 at adm
  change (submitResidentRow D S pad prior r).steps=read.steps+A.steps+3 at sub
  change (submitResidentRow D S pad prior r).steps=
    2*read.steps+query.steps+test.steps+ext.steps+ins.steps+14
  omega

theorem literal_outer_publication_is_the_true_publish_fee
    (i : Centre) (j : Sample) (g : Fin 64)
    (sync : prior.synced) (reserved : ∀ z∈prior.headers,z.id.bits.take kp≠D.mark.bits) :
    let r := sourceRow (W:=W) D i j g
    let job := cachedExteriorJob D S pad r
    (job.install prior).steps=publishFee prior job.entry job.offset job.built := by
  let r := sourceRow (W:=W) D i j g
  let X := actualExterior (W:=W) D r
  let K := S.exactRoot.trans (congrArg Meter.result (one_root_cache_for_every_entry (W:=W) D r))
  have id : (X.seed pad).identifier=X.issue.result := (stable_exterior_header X).1
  have marker : X.issue.result.bits.take kp=D.mark.bits :=
    actual_public_owner_marker W D i j g
  have fresh : ∀ row∈prior.headers,row.id≠(X.seed pad).identifier := by
    intro row h same
    apply reserved row h
    rw [same,id,marker]
  exact (prepared_seed_exact_install X S.root K pad prior sync fresh).2

def submittedRowRoof (m n key e install : ℕ) : ℕ :=
  2*((literalDegree m n+1)*(e+2))+lookupOuterRoof m n key+(5*e+2)+
    (ordinalFee 6 63+8)+install+14

theorem true_literal_submit_has_the_local_roof
    (i : Centre) (j : Sample) (g : Fin 64) (install : ℕ)
    (charged : ((cachedExteriorJob D S pad (sourceRow (W:=W) D i j g)).install prior).steps ≤ install) :
    (submitResidentRow D S pad prior (sourceRow (W:=W) D i j g)).steps ≤ submittedRowRoof m native (KeyWidth kp tc tj) f.natDegree install := by
  let r := sourceRow (W:=W) D i j g
  let read := S.requests.probes.read j
  let query := rawRequest D.mark r.wire S.requests.rows
  let test := eqRawBits read.result.val read.result.val
  let ext := entrySource (W:=W) D r
  let ins := (cachedExteriorJob D S pad r).install prior
  have lookup : query.steps ≤ lookupOuterRoof m native (KeyWidth kp tc tj) :=
    legal_outer_request_lookup_has_printed_bound D S i j g
  have probe : read.steps ≤ (literalDegree m native+1)*(f.natDegree+2) := real_probe_read_has_printed_bound D S j
  have cmp : test.steps ≤ 5*f.natDegree+2 := by
    have t := (eq_raw_bits_exact read.result.val read.result.val).2
    rw [read.result.property] at t
    exact t
  have loc := (entry_source_is_actual (W:=W) D r).2.2.2.2
  have ord := ordinal_fee_monotone 6 (Nat.le_of_lt_succ g.isLt)
  have extRoof : ext.steps ≤ ordinalFee 6 63+8 := by
    change ext.steps=ordinalFee 6 g.val+8 at loc
    rw [loc]
    omega
  have fee := literal_submit_uses_both_probe_reads D S pad prior i j g
  change (submitResidentRow D S pad prior r).steps=
    2*read.steps+query.steps+test.steps+ext.steps+ins.steps+14 at fee
  change ins.steps ≤ install at charged
  rw [fee,submittedRowRoof]
  omega

#print axioms resident_probe_input_has_the_original_tariff
#print axioms real_probe_read_has_printed_bound
#print axioms legal_outer_request_lookup_has_printed_bound
#print axioms literal_submit_uses_both_probe_reads
#print axioms literal_outer_publication_is_the_true_publish_fee
#print axioms true_literal_submit_has_the_local_roof
end
end J6R75OuterTime

