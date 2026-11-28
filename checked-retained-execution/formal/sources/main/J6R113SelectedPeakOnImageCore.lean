import J6R112ExecutedSelectedStartupPlan
import J6R111SameRunNames

/-! A local execution cut of the R112 selected image. The successful
R57 reply supplies the actual bank; the indexed published name is
used only as the proof that the continuation is well typed. -/
namespace J6R113SelectedPeakOnImage
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R34ChildPath J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer
open J6R51Online J6R52FreshExterior J6R57PublicRequest J6R54PublicFamily
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R28GeneratedRootFrame J6R14ZeroMode J6R34OfficialGateway
open J6R68ActiveInputs.Sweep J6R75OuterTime J6R19Retained J1PPrinted
open J6R31RootResidentTables J6R111SelectedGroup J6R108FinalDriver
open J6R112ExecutedSelectedStartup J6R64Active

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 23000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q rr cc dd prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (image : RequestImage W I) (plan : SelectedCountOnImage image)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
local notation "D" => image.compiled
local notation "S" => image.tables
local notation "r0" => (sourceRow (W:=W) image.compiled i j g)
local notation "Y" => (actualExterior (W:=W) image.compiled (sourceRow (W:=W) image.compiled i j g))
local notation "A" => (plan.plans i j g)
local notation "Q" => (plan.setups i j g)
local notation "Bank" => (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+plan.pad))

/-- Exactly the native continuation used by the admitted selected
group, with the chooser and chart taken from that image's one setup
at this actual public address. -/
def continuationOfTheSelectedHead (b : Bank)
    (ack : (submitResidentRow D S plan.pad plan.prior r0).result=some (b,true))
    (own : OwnsHeader (Y).header.result b) :=
  continueSelectedPublicGroup D S plan.pad plan.prior r0 Y
    (Q).paidChosen (A).keep (Q).paidChart (A).layout (A).retire b ⟨ack,own⟩

/-- This equality includes the actual address emission, physical row
source, prescribed admission, and the same acknowledged continuation.
There is no other probe bank, admission, or compiler in this cut. -/
theorem actual_paid_head_uses_that_successful_continuation
    (H : ExactHead m native tc tj tw i j) (same : H=(prepareHead W i j).result)
    (b : Bank) (ack : (submitResidentRow D S plan.pad plan.prior r0).result=some (b,true))
    (own : OwnsHeader (Y).header.result b) :
    let used := continuationOfTheSelectedHead image plan i j g b ack own
    let sent := emitEntry (D).mark (i,j) H g
    let source := entrySource (W:=W) D r0
    let reply := submitResidentRow D S plan.pad plan.prior r0
    paidSelectedAtHead D S plan.pad plan.prior plan.plans plan.sync plan.reserved
        plan.setups i j g H same =
      ⟨used.result.1, sent.steps+(source.steps+(reply.steps+used.steps+4)+3)+3⟩ := by
  subst H
  have sameBank := the_actual_R57_reply_is_the_proof_only_published_snapshot D S plan.pad
    plan.prior i j g plan.sync plan.reserved b ack
  subst b
  let p := entrySource (W:=W) D r0
  let e := emitEntry (D).mark (i,j) (prepareHead W i j).result g
  let read := runAdmittedSelectedPublicGroup D S plan.pad plan.prior r0 plan.sync plan.reserved
    (canonical_source_row_is_resident D S i j g) p.result rfl
    (Q).paidChosen (A).keep (Q).paidChart (A).layout (A).retire
  let v := continuationOfTheSelectedHead image plan i j g
    (publishedBank D S plan.pad plan.prior r0) ack own
  let reply := submitResidentRow D S plan.pad plan.prior r0
  have h : read=⟨v.result,reply.steps+v.steps+4⟩ :=
    actual_admit_select_and_recurse_are_three_paid_parts D S plan.pad plan.prior r0
      plan.sync plan.reserved (canonical_source_row_is_resident D S i j g) p.result rfl
      (Q).paidChosen (A).keep (Q).paidChart (A).layout (A).retire
  change (⟨read.result.1,e.steps+(p.steps+read.steps+3)+3⟩ : Meter _) =
    ⟨v.result.1,e.steps+(p.steps+(reply.steps+v.steps+4)+3)+3⟩
  rw [h]

#print axioms continuationOfTheSelectedHead
#print axioms actual_paid_head_uses_that_successful_continuation
end
end J6R113SelectedPeakOnImage

