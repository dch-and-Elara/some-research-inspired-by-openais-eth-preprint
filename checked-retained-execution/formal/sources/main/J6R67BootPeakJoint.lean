import J6R67BootPeakPublic
import J6R67BootPeakCanonical

/-! The metered composed run and the observers share one selected
request and one first-scope operation. The cuts are selected serializable
fields at those program boundaries, not a model of all live heap. -/
namespace J6R67.BootPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R57PublicRequest J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R48DFS J6R33StatefulArithmeticPage J6R30ProducedGateRegistry J6R51Peak
open J6R59Public J6R21Ancestor J6R32StatefulArithmetic J6R66.BootPeak
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4600
set_option Elab.async false

inductive PublicationCut where
  | exterior (pt : ExteriorPoint)
  | owner (pt : ℕ×ℕ)
  | assembling (pt : InitPoint)
  | preparedChild (pt : InitPoint)
  | installedChild (pt : InitPoint)

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P₀ : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P₀ (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable {I : SharedInputs G ell q rr cc dd prec kp bw}

variable {image : RequestImage W I} {pad : ℕ}
variable (Q : PublicRoot image pad)
variable {Out : Type}
variable (first : (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))→
  IsLive (Q.exterior.seed pad) bank→
  BootOp f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) Out)

def publicAndFirstScope : Meter
    (Out×PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) :=
  continueActualResult Q.submit Q.incoming Q.liveBank (actual_outer_bank_census Q).1
    (IsLive (Q.exterior.seed pad)) Q.live (fun found live=>(first found live).run found)

theorem actual_public_and_first_meter
    (legal : JobsReady Q.liveBank [(first Q.liveBank Q.live).job]) :
    let A := first Q.liveBank Q.live
    let R := A.inside Q.liveBank
    publicAndFirstScope Q first=
      ⟨(R.result.1,Q.liveBank),Q.submit.steps+
        (A.initial.steps+(A.publicationFee Q.liveBank+(A.installFee+R.steps)+A.retire A.job+4))+4⟩ := by
  let A := first Q.liveBank Q.live
  have ext := continuation_reads_the_returned_meter_result Q.submit Q.incoming Q.liveBank
    (actual_outer_bank_census Q).1 (IsLive (Q.exterior.seed pad)) Q.live
    (fun found live=>(first found live).run found)
  have child := (first_boot_uses_its_actual_child_bank_once A Q.liveBank legal).1
  exact ext.trans (congrArg (fun d : Meter
    (Out×PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))=>
      Meter.mk d.result (Q.submit.steps+d.steps+4)) child)

variable (F : FirstFootprint (first Q.liveBank Q.live))
variable (common : ℕ)

/-- Definitions only: no reader, copy, or footprint pass is performed
by publicAndFirstScope. The prepared-child payload is the same body
that is passed through Job.built and becomes resident at the next cut. -/
def namedPublicationCut : PublicationCut→ℕ
  | .exterior pt =>
    common+(mountedSelectedBits Q.incoming+Q.wordCut pt.header+Q.pageCut pt)
  | .owner pt =>
    common+(mountedSelectedBits Q.liveBank+F.sharedStart+F.mount.view pt)
  | .assembling pt =>
    common+(mountedSelectedBits Q.liveBank+F.sharedStart+F.boot.view pt)
  | .preparedChild pt =>
    common+(mountedSelectedBits Q.liveBank+F.sharedStart+F.boot.view pt+
      mountedInsertionBits (first Q.liveBank Q.live).job)
  | .installedChild pt =>
    common+(mountedSelectedBits (afterOne Q.liveBank (first Q.liveBank Q.live).job)+
      F.sharedStart+F.boot.view pt)

def publicationRoof : ℕ :=
  common+mountedSelectedBits Q.incoming+
    max (Q.wordRoof+Q.pageRoof)
      (mountedInsertionBits Q.outerJob+F.sharedStart+
        max F.mount.roof (F.boot.roof+mountedInsertionBits (first Q.liveBank Q.live).job))

theorem simultaneous_named_publication_fields_fit (cut : PublicationCut) :
    namedPublicationCut Q first F common cut ≤ publicationRoof Q first F common := by
  let outer := Q.wordRoof+Q.pageRoof
  let before := mountedSelectedBits Q.incoming
  let live := mountedSelectedBits Q.liveBank
  let pub := mountedInsertionBits Q.outerJob
  let child := mountedInsertionBits (first Q.liveBank Q.live).job
  let localBound := max F.mount.roof (F.boot.roof+child)
  have hLive : live=before+pub := (actual_outer_bank_census Q).2
  have hChild :
      mountedSelectedBits (afterOne Q.liveBank (first Q.liveBank Q.live).job)=live+child :=
    publication_adds_exact_selected_record Q.liveBank (first Q.liveBank Q.live).job
  have a : outer≤max outer (pub+F.sharedStart+localBound) := le_max_left .. 
  have b : pub+F.sharedStart+localBound≤max outer (pub+F.sharedStart+localBound) := le_max_right ..
  have c : F.mount.roof≤localBound := le_max_left ..
  have d : F.boot.roof+child≤localBound := le_max_right ..
  have e : F.boot.roof≤F.boot.roof+child := Nat.le_add_right _ _
  have cap : publicationRoof Q first F common=
      common+before+max outer (pub+F.sharedStart+localBound) := rfl
  rw [cap]
  cases cut with
  | exterior pt =>
    change common+(before+Q.wordCut pt.header+Q.pageCut pt)≤_
    have h := Nat.add_le_add (actual_outer_publish_word_cut Q pt.header) (actual_outer_publish_page_cut Q pt)
    change Q.wordCut pt.header+Q.pageCut pt≤outer at h
    omega
  | owner pt =>
    change common+(live+F.sharedStart+F.mount.view pt)≤_
    have h := F.mount.within pt
    omega
  | assembling pt =>
    change common+(live+F.sharedStart+F.boot.view pt)≤_
    have h := F.boot.within pt
    omega
  | preparedChild pt =>
    change common+(live+F.sharedStart+F.boot.view pt+child)≤_
    have h := F.boot.within pt
    omega
  | installedChild pt =>
    change common+(mountedSelectedBits (afterOne Q.liveBank (first Q.liveBank Q.live).job)+
      F.sharedStart+F.boot.view pt)≤_
    have h := F.boot.within pt
    omega

#print axioms publicAndFirstScope
#print axioms actual_public_and_first_meter
#print axioms simultaneous_named_publication_fields_fit
end
end J6R67.BootPeak
