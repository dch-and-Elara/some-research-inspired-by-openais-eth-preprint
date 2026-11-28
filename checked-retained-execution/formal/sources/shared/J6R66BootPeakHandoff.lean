import J6R66BootPeakMount
import J6R64BootSeatsInstall

/-! Typed handoff of the exact live bank returned by R57's actual
successful public submit. A dependent R55 initializer may consume this
same bank without a second exterior install. The initializer's own
Meter is visibly charged; no theorem claims to construct its source
operands. -/
namespace J6R66.BootPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R57PublicRequest J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R48DFS J6R33StatefulArithmeticPage J6R30ProducedGateRegistry J6R51Peak
open J6R59Public J6R21Ancestor J6R32StatefulArithmetic
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12500000
set_option maxRecDepth 4200
set_option Elab.async false

def continueActualResult {L Out : Type*} (A : Meter (Option (L×Bool))) (original expected : L)
    (success : A.result=some (expected,true)) (P : L→Prop) (good : P expected)
    (go : (found : L) → P found → Meter Out) : Meter Out :=
  let actual := A.result.getD (original,false)
  have eq : actual.1=expected :=
    congrArg (fun got : Option (L×Bool)=>(got.getD (original,false)).1) success
  let done := go actual.1 (eq.symm ▸ good)
  ⟨done.result,A.steps+done.steps+4⟩

theorem continuation_reads_the_returned_meter_result {L Out : Type*}
    (A : Meter (Option (L×Bool))) (original expected : L)
    (success : A.result=some (expected,true)) (P : L→Prop) (good : P expected)
    (go : (found : L) → P found → Meter Out) :
    continueActualResult A original expected success P good go=
      ⟨(go expected good).result,A.steps+(go expected good).steps+4⟩ := by
  cases A with
  | mk result steps =>
    change result=some (expected,true) at success
    subst result
    rfl

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable (r : Entry D.mark m native tc tj tw)
variable (sync : B.synced) (reserved : ∀ x∈B.headers,x.id.bits.take kp≠D.mark.bits)
variable (stored : r∈S.requests.rows)
variable {Out : Type}
variable (go : (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))→
    IsLive ((entrySource (W:=W) D r).result.seed pad) bank → Meter Out)

def actualAdmissionThen : Meter Out :=
  let legal := accepted_entry_installs_that_actual_job D S pad B r sync reserved stored
  continueActualResult (submitResidentRow D S pad B r) B
    (afterOne B (cachedExteriorJob D S pad r)) legal.1
    (IsLive ((entrySource (W:=W) D r).result.seed pad)) legal.2.1 go

theorem public_dependent_boot_consumes_the_same_single_publication :
    let legal := accepted_entry_installs_that_actual_job D S pad B r sync reserved stored
    let j := cachedExteriorJob D S pad r
    let out := go (afterOne B j) legal.2.1
    actualAdmissionThen D S pad B r sync reserved stored go=
      ⟨out.result,(submitResidentRow D S pad B r).steps+out.steps+4⟩ ∧
    mountedSelectedBits (afterOne B j)=mountedSelectedBits B+mountedInsertionBits j :=
  let h := accepted_entry_installs_that_actual_job D S pad B r sync reserved stored
  ⟨continuation_reads_the_returned_meter_result _ _ _ h.1 _ h.2.1 go,h.2.2⟩

#print axioms continuation_reads_the_returned_meter_result
#print axioms actualAdmissionThen
#print axioms public_dependent_boot_consumes_the_same_single_publication
end
end J6R66.BootPeak
