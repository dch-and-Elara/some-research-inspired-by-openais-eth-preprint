import J6R116RunReadyRetainedPayload
import J6R115AdmittedExecutionImage

/-! Assembly over the one returned request image. For each real group
address, the preparer takes the actual held payload; the original
addresses index the result, not a second evaluation. -/
namespace J6R114PrescribedReceipts
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J6OrientedHostEval J6R51Ingress
open J6R54PublicFamily J6R57PublicRequest J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R22RootReadout J6R75OuterTime J6R36SharedGateway J6R33OriginalJ6 J6R34OfficialGateway
open J6R25StableCensus J6R15ModeCost J6R11Repack J6R24MeteredRecursion
open J6R24LegalLayout J6R26StablePreparedRoot J6R31RootResidentTables J1PPrinted
open J6R14ZeroMode J6R19Retained J6R12Blueprint J6R33StatefulArithmeticPage
open J6R34RootAtlas J6R50SourceProducer J6R52FreshExterior J6R111KeptOwnerFlow

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5200
set_option maxHeartbeats 15000000
set_option maxSynthPendingDepth 10

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q rr cc dd prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

def typedOriginalGroup {h h' : f.Monic}
    {i i' : J6Recovery.Addr m} {j j' : Fin (literalDegree m native+1)} {g g' : Fin 64}
    (hi : i'=i) (hj : j'=j) (hg : g'=g)
    (received : GroupReceipt (ell:=ell) G h' i' j' g') :
    GroupReceipt (ell:=ell) G h i j g := by
  subst i'
  subst j'
  subst g'
  exact received

theorem typed_group_does_not_change_the_actual_steps {h h' : f.Monic}
    {i i' : J6Recovery.Addr m} {j j' : Fin (literalDegree m native+1)} {g g' : Fin 64}
    (hi : i'=i) (hj : j'=j) (hg : g'=g)
    (received : GroupReceipt (ell:=ell) G h' i' j' g') :
    (typedOriginalGroup (h:=h) hi hj hg received).run.steps=received.run.steps := by
  cases hi
  cases hj
  cases hg
  rfl

variable (image : RequestImage W I)

structure PhysicalRetainedImagePlan where
  pad : ℕ
  prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)
  sync : prior.synced
  reserved : ∀ h∈prior.headers,h.id.bits.take kp≠image.compiled.mark.bits
  acquire : ∀ i j g r,
    r=sourceRow (W:=W) image.compiled i j g →
    (reply : AdmittedAtAddress image.compiled image.tables pad prior i j g r) →
    Meter (ReadyRetainedPayload reply.payload)
  acquireScale : ∀ i j g r sameRow reply,
    let actual := acquire i j g r sameRow reply
    actual.result.size=physicalSize m native ∧ actual.result.constant=2 ∧
      HEq actual.result.selector (G.selector ell)

variable (Q : PhysicalRetainedImagePlan image)

theorem actual_posted_payload_has_source_scale
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
    let row := sourceRow (W:=W) image.compiled i j g
    let posted := admitTheEmittedRow image.compiled image.tables Q.pad Q.prior Q.sync Q.reserved i j g row rfl
    let actual := Q.acquire i j g row rfl posted.result
    actual.result.size=physicalSize m native ∧ actual.result.constant=2 ∧
      HEq actual.result.selector (G.selector ell) :=
  Q.acquireScale i j g _ rfl _

def physicalRowsOnThatImage : PaidRowsOnImage image :=
  fun i j g r sameRow _ =>
    let posted := admitTheEmittedRow image.compiled image.tables Q.pad Q.prior Q.sync Q.reserved
      i j g r sameRow
    let a := posted.result
    let data := Q.acquire i j g r sameRow a
    let run := measuredRetainedPhysicalGroup a.payload data a.owns a.live
    have hi : a.payload.site.centre=i := (congrArg StableExterior.centre a.selectedSite).trans rfl
    have hj : a.payload.site.sample=j := (congrArg StableExterior.sample a.selectedSite).trans rfl
    have hg : a.payload.site.group=g := (congrArg StableExterior.group a.selectedSite).trans rfl
    let typed := typedOriginalGroup hi hj hg run
    ⟨typed.frame,⟨typed.run.result,posted.steps+typed.run.steps+3⟩,typed.truth⟩

def runPhysicalRetainedCountAtImage : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  paidCountOnImage image (physicalRowsOnThatImage image Q)

theorem the_same_ready_physical_image_returns_the_guarded_count
    (positiveBase : 0<base) (zeroOpening : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    bitsValue (runPhysicalRetainedCountAtImage image Q).result.val=answer :=
  the_exact_addressed_image_count image (physicalRowsOnThatImage image Q)
    positiveBase zeroOpening answer count

#print axioms actual_posted_payload_has_source_scale
#print axioms typed_group_does_not_change_the_actual_steps
#print axioms runPhysicalRetainedCountAtImage
#print axioms the_same_ready_physical_image_returns_the_guarded_count
end
end J6R114PrescribedReceipts

