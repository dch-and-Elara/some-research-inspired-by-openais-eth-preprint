import J6R67BootPeakJoint
import J6R67BootPeakFactory

/-! Final same-operation receipt. The shared image is the original
generated R57 RequestImage, the returned bank is used by the
dependent R55 plan, and the first completed job uses that very
compiled body through the original publish/install interpreter. -/
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
set_option maxHeartbeats 10600000
set_option maxRecDepth 4600
set_option Elab.async false

section PreparedBody
variable {f : ℤ[X]} {ell key prec tw bw page : ℕ} {Out : Type}
variable (A : BootOp f ell key prec tw bw page Out)

noncomputable def firstPreparedPayloadBits : ℕ :=
  insertionBits A.job+
    ((A.job.built.result.map (fun payload=>
      ((envelopePages payload).map List.length).sum+frameWordsBits payload.shape)).getD 0)

theorem first_prepared_meter_contains_the_observed_body :
    firstPreparedPayloadBits A=mountedInsertionBits A.job := by
  unfold firstPreparedPayloadBits mountedInsertionBits
  rw [A.job.validBody]
  simp only [Option.map_some,Option.getD_some,Nat.add_assoc]
end PreparedBody

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {P₀ : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P₀ (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable (W : Widths m native tc tj tw edgew)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (I : SharedInputs G ell q rr cc dd prec kp bw)
variable {image : RequestImage W I} {pad : ℕ}
variable (Q : PublicRoot image pad)
variable {Out : Type}
variable (plan : FirstPlan (Q.exterior.seed pad) Out)

def runPreparedR57andFirst : Meter (Out×PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) :=
  publicAndFirstScope Q plan.call

theorem actual_image_and_first_publication_bound
    (fromRealImage : image=(buildRequestImage W I).result)
    (ready : JobsReady Q.liveBank [(plan.call Q.liveBank Q.live).job]) :
    let liveOp := plan.call Q.liveBank Q.live
    let footprint := plan.observe Q.liveBank Q.live
    let current := liveOp.inside Q.liveBank
    runPreparedR57andFirst (W:=W) (I:=I) Q plan=
      ⟨(current.result.1,Q.liveBank),Q.submit.steps+
        (liveOp.initial.steps+(liveOp.publicationFee Q.liveBank+(liveOp.installFee+current.steps)+liveOp.retire liveOp.job+4))+4⟩ ∧
    bitSize entryBits image.tables.requests.rows=publicCount m native*entryWidth kp tc tj tw ∧
    firstPreparedPayloadBits liveOp=mountedInsertionBits liveOp.job ∧
    (∀ pt : PublicationCut,
      namedPublicationCut Q plan.call footprint (sharedRequestBits W I) pt≤
      publicationRoof Q plan.call footprint (sharedRequestBits W I)) := by
  refine ⟨actual_public_and_first_meter Q plan.call ready,?_,
    first_prepared_meter_contains_the_observed_body _,fun pt=>
      simultaneous_named_publication_fields_fit Q plan.call (plan.observe Q.liveBank Q.live)
        (sharedRequestBits W I) pt⟩
  change bitSize entryBits image.tables.requests.rows=_
  rw [fromRealImage]
  exact actual_request_image_has_exact_catalogue_bits W I

#print axioms first_prepared_meter_contains_the_observed_body
#print axioms runPreparedR57andFirst
#print axioms actual_image_and_first_publication_bound
end
end J6R67.BootPeak
