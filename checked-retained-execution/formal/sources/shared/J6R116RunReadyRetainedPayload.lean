import J6R116ReadyRetainedPayload
import J6R111KeptOwnerFlowSharedConsume

/-! Run the prepared, addressed continuation on the retained carrier's
actual site and bank. The preparer is charged, and no old group executes. -/
namespace J6R111KeptOwnerFlow
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6OrientedHost J6OrientedHostEval J6Mesh
open J6R57PublicRequest J6R54PublicFamily J6R52FreshExterior J6R34OfficialGateway
open J6R34RootAtlas J6R33StatefulArithmeticPage J6R64Active J6R30ProducedGateRegistry
open J6R35GatewayPreparation J6R24MeteredRecursion J6R12Blueprint J6R11Blueprint
open J6R28GeneratedRootFrame J6R26StablePreparedRoot J6R27PrescribedProbe J1PPrinted
open J6R24LegalLayout J6R31RootResidentTables J6R14ZeroMode J6R19Retained J6R10Reachable
open J6R32StatefulArithmetic J6R32RootGeneratedRegistryInputs

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5100
set_option maxHeartbeats 15000000

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj kp prec tw bw : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable {Cpt : Compiled G ell q ro co de prec kp bw} {pad : ℕ}

variable (a : ResidentAdmissionCarry (W:=W) Cpt pad)
variable (pay : Meter (ReadyRetainedPayload a))
variable (owns : OwnsHeader a.site.header.result a.receipt.1)
variable (live : IsLive (a.site.seed pad) a.receipt.1)

def measuredRetainedPhysicalGroup :
    GroupReceipt (ell:=ell) G a.site.hf a.site.centre a.site.sample a.site.group :=
  let A := pay.result
  letI := sourceDecision A.selector (exteriorChild G ell a.site.centre a.site.sample a.site.group)
  let native := consumeAdmittedKeptGroup a A.machine owns A.first A.drivers A.exterior A.retire
    A.gate A.boot A.gateWidth A.basePositive (fun {_} p w=>A.valid p w) live A.zeroBranch
    A.exteriorStop A.degreePositive
  ⟨native.frame,⟨native.run.result,pay.steps+native.run.steps+4⟩,native.truth⟩

theorem the_paid_group_runs_from_that_one_returned_bank_and_data :
    let A := pay.result
    let direct := runRetainedExterior a.site A.machine a.receipt.1 owns A.first A.drivers A.exterior A.retire
    (measuredRetainedPhysicalGroup a pay owns live).run.steps=pay.steps+direct.steps+4 := rfl

#print axioms measuredRetainedPhysicalGroup
#print axioms the_paid_group_runs_from_that_one_returned_bank_and_data
end
end J6R111KeptOwnerFlow

