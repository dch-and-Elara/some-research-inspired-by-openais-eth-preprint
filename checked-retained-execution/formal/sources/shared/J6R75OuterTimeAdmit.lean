import J6R75OuterTimeHead
import J6R66BootPeakHandoff
import J6R68ActiveInputsSweepRun

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3200
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Run the raw-centre R68 contraction on the *returned* bank of the
actual R57 publication. The bank in the proof is merely the verified
normal form of that publication; its installer is not called twice. -/
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
open J6R63Active J6R62ActivePrep

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
theorem literal_exterior_owns_the_installed_head
    (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
    (pad : ℕ) (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) (r : Entry D.mark m native tc tj tw)
    (Y : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw) (same : Y=actualExterior (W:=W) D r) :
    OwnsHeader Y.header.result (publishedBank D S pad prior r) := by
  subst Y
  exact published_head_is_the_actual_raw_header D S pad prior r

variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}

def runAdmittedRaw
    (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
    (pad : ℕ) (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) (r : Entry D.mark m native tc tj tw)
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (written : r∈S.requests.rows)
    (Y : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw) (same : Y=actualExterior (W:=W) D r)
    {T : Prepared cfg sel (exteriorChild G ell Y.centre Y.sample Y.group) Y.hf}
    (M : OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
    (F : RetainedAfter T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate cw)
    (chart : MountedChart T)
    (layout : ExteriorLayout (T:=T) (page:=pageKeyWidth m+pad) (cw:=cw) Y)
    (retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→ℕ) :
    Meter (Block (T.frame (Path.root : Path sel (exteriorChild G ell Y.centre Y.sample Y.group) (exteriorChild G ell Y.centre Y.sample Y.group)).reached) ell×PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) :=
  let legal := accepted_entry_installs_that_actual_job D S pad prior r sync reserved written
  continueActualResult (submitResidentRow D S pad prior r) prior (publishedBank D S pad prior r) legal.1
    (OwnsHeader Y.header.result) (literal_exterior_owns_the_installed_head D S pad prior r Y same)
    (fun live owns=>runRawPhysicalExterior Y M F chart layout retire live owns)

theorem publication_then_raw_is_one_actual_meter
    (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
    (pad : ℕ) (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) (r : Entry D.mark m native tc tj tw)
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (written : r∈S.requests.rows)
    (Y : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw) (same : Y=actualExterior (W:=W) D r)
    {T : Prepared cfg sel (exteriorChild G ell Y.centre Y.sample Y.group) Y.hf}
    (M : OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
    (F : RetainedAfter T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate cw)
    (chart : MountedChart T)
    (layout : ExteriorLayout (T:=T) (page:=pageKeyWidth m+pad) (cw:=cw) Y)
    (retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→ℕ) :
    let raw := runRawPhysicalExterior Y M F chart layout retire (publishedBank D S pad prior r) (literal_exterior_owns_the_installed_head D S pad prior r Y same)
    runAdmittedRaw D S pad prior r sync reserved written Y same M F chart layout retire=
      ⟨raw.result,(submitResidentRow D S pad prior r).steps+raw.steps+4⟩ := by
  let legal := accepted_entry_installs_that_actual_job D S pad prior r sync reserved written
  exact continuation_reads_the_returned_meter_result (submitResidentRow D S pad prior r) prior
    (publishedBank D S pad prior r) legal.1 (OwnsHeader Y.header.result)
    (literal_exterior_owns_the_installed_head D S pad prior r Y same)
    (fun live owns=>runRawPhysicalExterior Y M F chart layout retire live owns)

theorem no_republication_between_receipt_and_contraction
    (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
    (pad : ℕ) (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) (r : Entry D.mark m native tc tj tw)
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (written : r∈S.requests.rows)
    (Y : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw) (same : Y=actualExterior (W:=W) D r)
    {T : Prepared cfg sel (exteriorChild G ell Y.centre Y.sample Y.group) Y.hf}
    (M : OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
    (F : RetainedAfter T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate cw)
    (chart : MountedChart T)
    (layout : ExteriorLayout (T:=T) (page:=pageKeyWidth m+pad) (cw:=cw) Y)
    (retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→ℕ) :
    (runAdmittedRaw D S pad prior r sync reserved written Y same M F chart layout retire).result.2=publishedBank D S pad prior r := by
  have receipt := publication_then_raw_is_one_actual_meter D S pad prior r sync reserved written Y same
    M F chart layout retire
  have back := raw_root_restores_actual_bank M F chart (physicalExteriorInputs Y layout) retire
    (publishedBank D S pad prior r) (literal_exterior_owns_the_installed_head D S pad prior r Y same)
  exact (congrArg Prod.snd (congrArg Meter.result receipt)).trans back

theorem admitted_raw_group_has_its_own_additive_bill
    (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
    (pad : ℕ) (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) (r : Entry D.mark m native tc tj tw)
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (written : r∈S.requests.rows)
    (Y : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw) (same : Y=actualExterior (W:=W) D r)
    {T : Prepared cfg sel (exteriorChild G ell Y.centre Y.sample Y.group) Y.hf}
    (M : OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
    (F : RetainedAfter T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate cw)
    (chart : MountedChart T)
    (layout : ExteriorLayout (T:=T) (page:=pageKeyWidth m+pad) (cw:=cw) Y)
    (retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→ℕ)
    (localCap : ℕ) (paid : (runRawPhysicalExterior Y M F chart layout retire (publishedBank D S pad prior r) (literal_exterior_owns_the_installed_head D S pad prior r Y same)).steps≤localCap) :
    (runAdmittedRaw D S pad prior r sync reserved written Y same M F chart layout retire).steps≤(submitResidentRow D S pad prior r).steps+localCap+4 := by
  have receipt := publication_then_raw_is_one_actual_meter D S pad prior r sync reserved written Y same
    M F chart layout retire
  exact (congrArg Meter.steps receipt).trans_le (Nat.add_le_add_right (Nat.add_le_add_left paid _) _)

#print axioms literal_exterior_owns_the_installed_head
#print axioms runAdmittedRaw
#print axioms publication_then_raw_is_one_actual_meter
#print axioms no_republication_between_receipt_and_contraction
#print axioms admitted_raw_group_has_its_own_additive_bill
end
end J6R75OuterTime

