import J6R55PublicFamily
import J6R54PublicFamilyCountFresh

/-! Final fresh CNF readout on the generated public job family. No
separate readiness, liveness, edge-order or PublicJobs witness is supplied. -/
namespace J6R55Public
open scoped Classical Polynomial
open Polynomial Std.Sat AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R22RootReadout
open J6R51Ingress J6R52FreshShape J7R9Compiler J7R9Subdivision J7R10Plant
open J6R53PublicMount J6R49RootIngress J6R50RootIngress J6R54PublicFamily
open J6R32RootGeneratedRegistryInputs J6R33StatefulArithmeticPage J6R34RootAtlas J6R14ZeroMode J6R31RootResidentTables J6R16ModeCost
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 22000000
set_option maxRecDepth 4500
set_option Elab.async false
attribute [local irreducible] J6R51Ingress.freshPlant J6R51Ingress.guardedInOrder
attribute [local irreducible] runMountedCount runPreparedCount

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable (F : CNF V) (order : DeclaredOrder V)
variable {f : ℤ[X]} {base native ell q rr cc dd edgew tc tj prec tw bw rate pad kp : ℕ}
variable (G : RootShape f (nWires (guardedInOrder F order.roster))
  (printedHalf (nWires (guardedInOrder F order.roster))) base native
  (printedRankWidth (nWires (guardedInOrder F order.roster)))
  (freshPlant (guardedInOrder F order.roster) (guardRoster order))
  (constantRootWord (nWires (guardedInOrder F order.roster))))
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (I : SharedInputs G ell q rr cc dd prec kp bw)
variable (W : Widths (nWires (guardedInOrder F order.roster)) native tc tj tw edgew)
variable (bp : 0<base)
variable (D : ∀ i j g, EmittedSiteDriver W (prepareShared I).result rate pad bp i j g)
variable (B : reservedBank (f:=f) (ell:=ell) (kp:=kp) (tc:=tc) (tj:=tj)
  (prec:=prec) (tw:=tw) (bw:=bw) (m:=nWires (guardedInOrder F order.roster)) pad)
variable (retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw
  (pageKeyWidth (nWires (guardedInOrder F order.roster))+pad)→ℕ)

theorem actual_emitted_driver_CNF_count_and_bill
    (sync : B.synced) (old : ∀ row∈B.headers,row.id.val≤(prepareShared I).result.mark.val)
    (slack : 2*nWires (guardedInOrder F order.roster)+1+
      pathLimit (physicalSize (nWires (guardedInOrder F order.roster)) native) 2<2^tc) :
    let S := prepareShared I
    let jobs := publicJobsOfEmittedDrivers W S.result bp D B retire sync old slack
    let out := runPreparedCount W I jobs
    let orig := runMountedCount G S.result.hf S.result.frame S.result.positive (plainFamily W S.result jobs)
    bitsValue out.result.val=PinnedCNF.modelCount F ∧
      out.steps=orig.steps+S.steps+allLocationFee W := by
  dsimp only
  let S := prepareShared I
  let jobs := publicJobsOfEmittedDrivers W S.result bp D B retire sync old slack
  exact ⟨actual_prepared_fresh_CNF_word F order G I W jobs bp,
    (prepared_count_same_word_and_exact_full_bill W I jobs).2⟩

#print axioms actual_emitted_driver_CNF_count_and_bill
end
end J6R55Public
