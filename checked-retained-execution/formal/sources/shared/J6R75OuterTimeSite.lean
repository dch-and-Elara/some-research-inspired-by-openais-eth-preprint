import J6R75OuterTimeSlot

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 26000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! The actual prescribed R36 packet/interpolation consumes the measured
64-group R75 slot on the retained R57 probe bank. The comparison oracle
is proof-only. Its fee is never used as the total charged cost. -/
namespace J6R75OuterTime
open scoped Polynomial Classical BigOperators
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
open J6R36SharedGateway J6R19Retained AOracleMachineTimeTape A1R10 A1R12
open J6R34OfficialGateway J6R68AbsolutePrescribed
open J6R33OriginalJ6 J6R25StableCensus J6R22RootReadout J6R11Repack J6OrientedHostEval
open J6R63Active J6R62ActivePrep J6R14ZeroMode

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))


local notation "Centre" => (J6Recovery.Addr m)
local notation "Sample" => (Fin (literalDegree m native+1))


variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable (R : RawGroupPlans D S pad B cfg rate cw)
variable (sync : B.synced) (reserved : ∀ x∈B.headers,x.id.bits.take kp≠D.mark.bits)
variable (frame : Frame f (J6SourcePrecision.printed m base))
variable (hv : 0<ell)

def outerOracle : CompletedOracle G ell frame D.hf :=
  completedOracle G D.hf frame hv (fun i j g=>verifiedSourceGroup D S pad B R sync reserved i j g (prepareHead W i j).result rfl)

theorem paid_raw_legal_slot_has_the_same_value (i : Centre) (j : Sample)
    (raw : List Bool) (legal : raw=List.ofFn ((rootPreset G ell).word j)) :
    (paidRawSlot D S pad B R sync reserved frame hv i j raw).result=
      (outerOracle D S pad B R sync reserved frame hv).reply i j raw := by
  have eq := paid_raw_slot_recovers_the_original_completed_product D S pad B R sync reserved frame hv i j raw
  refine (congrArg Meter.result eq).trans ?_
  exact (gateway_reply_exact G D.hf frame hv (fun a b g=>verifiedSourceGroup D S pad B R sync reserved a b g (prepareHead W a b).result rfl)
    i j raw legal).1.symm

def rawOuterSite (i : Centre) : Meter (Block frame ell) :=
  paidSite (F:=frame) G S.requests.probes (paidRawSlot D S pad B R sync reserved frame hv) D.hf hv i

def rawOuterSlotBill (i : Centre) : ℕ :=
  ((probeOrder (literalDegree m native+1)).map (fun j=>
    (paidRawSlot D S pad B R sync reserved frame hv i j (S.requests.probes.read j).result.val).steps)).sum

theorem each_outer_site_pays_the_actual_public_replies_once (i : Centre) :
    Delta (rawOuterSite D S pad B R sync reserved frame hv i)
      (oracleSite G S.requests.probes (outerOracle D S pad B R sync reserved frame hv) hv i)
      (rawOuterSlotBill D S pad B R sync reserved frame hv i) :=
  actual_paid_site_delta G S.requests.probes (paidRawSlot D S pad B R sync reserved frame hv)
    (outerOracle D S pad B R sync reserved frame hv)
    (fun i j raw good=>paid_raw_legal_slot_has_the_same_value D S pad B R sync reserved frame hv i j raw good) hv i

#print axioms outerOracle
#print axioms paid_raw_legal_slot_has_the_same_value
#print axioms rawOuterSite
#print axioms each_outer_site_pays_the_actual_public_replies_once
end
end J6R75OuterTime

