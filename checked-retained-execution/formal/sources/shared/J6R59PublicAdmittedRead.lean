import J6R57PublicRequestLive

namespace J6R59Public
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R33StatefulArithmeticPage
open J6R31RootResidentTables J6R30ProducedGateRegistry J6R32StatefulArithmetic
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4800
set_option Elab.async false
noncomputable section
section Admission
open J6R57PublicRequest
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (C : Compiled G ell q rr cc dd prec kp bw)
variable (S : InstalledRequestInputs W C) (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable (row : Entry C.mark m native tc tj tw)
variable {Out : Type}
variable (go : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→Meter Out)
variable (bad : Meter Out)

def useAdmittedResidentRow : Meter Out :=
  let A := submitResidentRow C S pad B row
  match A.result with
  | some (live, true) =>
    let done := go live
    ⟨done.result,A.steps+done.steps+4⟩
  | _ => ⟨bad.result,A.steps+bad.steps+4⟩

theorem original_admission_passes_its_actual_live_bank_once
    (sync : B.synced) (reserved : ∀ x∈B.headers,x.id.bits.take kp≠C.mark.bits)
    (stored : row∈S.requests.rows) :
    ∃ live,IsLive ((entrySource (W:=W) C row).result.seed pad) live ∧
      useAdmittedResidentRow C S pad B row go bad=
      ⟨(go live).result,(submitResidentRow C S pad B row).steps+(go live).steps+4⟩ := by
  obtain ⟨live,found,ok,_⟩ :=
    generated_public_row_returns_live_original_bank C S pad B sync reserved row stored
  refine ⟨live,ok,?_⟩
  unfold useAdmittedResidentRow
  dsimp only
  rw [found]
end Admission

#print axioms useAdmittedResidentRow
#print axioms original_admission_passes_its_actual_live_bank_once
end
end J6R59Public
