import J6R34RootAtlasStable
import J6R34RootAtlasLive

/-! The exterior root is the actual J6 prescribed zero child and is
not converted to an ordinary native Probe. Its one published atlas
and each paid descendant compiler feed the same live interpreter. -/
namespace J6R34RootAtlas
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R30ProducedGateRegistry
open J6R32RootGeneratedRegistryInputs J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6R14ZeroMode J6R27PrescribedProbe J6R26StablePreparedRoot J6R16ModeCost
open J6ActiveRun J6ActiveSchedule J6R9Recursive J1PPrinted J6R12Blueprint J6R11Blueprint J6R10Reachable
open J6R21Ancestor

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q r c d edgew tc tj key prec tw bw s C : ℕ}
variable (X : StableExterior G ell q r c d edgew tc tj key prec tw bw)
variable (pad : ℕ)
local notation "W" => (pageKeyWidth m+pad)
local notation "child" => (exteriorChild G ell X.centre X.sample X.group)
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {P : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem actual_prescribed_atlas_and_child_execution
    (descendantInputs : InputFamily P key prec tw bw W) (routes : RoutedInputs descendantInputs (X.seed pad))
    (B : PageBank f ell key prec tw bw W)
    (ready : JobsReady B (X.seed pad::(pagedLog (compilerResident descendantInputs (X.seed pad) routes) child .root).jobs)) :
    let seat := X.seed pad
    let live := compilerResident descendantInputs seat routes
    let log := Log.enter seat (pagedLog live child .root)
    let out := startFromAtlas live seat B
    (P.frame (.reflexive child)).decode out.result.1=reduce (child).prec f ell ((child).host.contract X.hf) ∧
      out.result.2=afterJobs B log.jobs ∧
      out.steps=(reference P child (.reflexive child)).steps+chronologicalBill B log.jobs+log.extras B ∧
      seat.identifier=X.issue.result ∧ seat.immutable.payload.stamp.created.val=(child).prec ∧
      (∀ k : Page (a m) (K m) (Fin 64),
        (locate (widened pad (residentPageKey m k)).result seat.immutable.payload.payload.pages).result=
          some (X.chosenFields k)) := by
  obtain ⟨word,state,fees⟩ := built_children_and_root_run descendantInputs (X.seed pad) routes B ready
  have h := stable_exterior_header X
  have fresh : ∀ row∈B.headers,row.id≠X.issue.result := by
    intro row row_at
    have neg := ready.2.2 (X.seed pad) List.mem_cons_self row row_at
    exact fun e=>neg (e.trans h.1.symm)
  dsimp only
  refine ⟨word,state,fees,h.1,h.2.2,?_⟩
  intro p
  exact (true_exterior_seed_lookup X pad B ready.1 fresh p).2.2.2.1

#print axioms actual_prescribed_atlas_and_child_execution
end J6R34RootAtlas
