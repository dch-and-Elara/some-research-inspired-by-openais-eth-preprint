import J6R68CanonicalRootWriterProvider
import J6R66ActiveExterior

/-! Use the canonical raw provider inside the verified physical runner,
not a second comparison run. On the actual stopping branch both input
producers occur exactly once in the runner's own Meter. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6ActiveRun J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R67CanonicalStop J6R11Blueprint J6R49Leaf J6R51Leaf J6R34ChildPath
open J6R24MeteredRecursion J6R51Online J1PPrinted J6R10Reachable J6R30ProducedGateRegistry
open J6R64Active J6R66Active J6R54ExteriorOwner J6R50SourceProducer J6R50Leaf J6R52Terminal

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15500000
set_option maxRecDepth 4900
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw s C rate own old cw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "N0" => (exteriorChild G ell X.centre X.sample X.group).edges
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Here" => (Path.root : Path sel
  (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group))
local notation "Machine" => (OnlineMachine T key prec tw bw Pg rate)
local notation "Bank" => (PageBank f ell key prec tw bw Pg)
variable (A : RootStopInputs X gate pad own old)

theorem physical_root_stop_runs_exact_paid_provider (M : Machine)
    (Rtn : RetainedAfter T key prec tw bw Pg rate cw)
    (layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=cw) X)
    (retire : PageJob f ell key prec tw bw Pg→ℕ)
    (B : Bank) (head : OwnsHeader X.header.result B)
    (stop : N0≤(printedParams (f:=f) (ell:=ell) s).cutoff) :
    let F := T.frame (Here).reached
    let ready := meteredRootStop X gate pad A F B
    runPhysicalExterior X (withCanonicalRootWriter X gate pad A M) Rtn layout retire B head=
      ⟨(ready.result,B),ready.steps⟩ := by
  unfold runPhysicalExterior
  rw [J6R66Active.runRoot,dif_pos stop]
  rfl

variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]

theorem same_original_stopped_run_charges_both_root_producers
    (M : Machine) (Rtn : RetainedAfter T key prec tw bw Pg rate cw)
    (layout : ExteriorLayout (T:=T) (page:=Pg) (cw:=cw) X)
    (retire : PageJob f ell key prec tw bw Pg→ℕ)
    (B : Bank) (head : OwnsHeader X.header.result B) (live : IsLive (X.seed pad) B)
    (stop : N0≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (basePos : 0<base) (nameInj : Function.Injective A.localName)
    (srcInj : Function.Injective A.sourceName) (gateWidth : gate.created.val=base)
    (hb : 0<A.codeWidth) (fit : N0≤2^A.codeWidth) :
    let F := T.frame (Here).reached
    let edgeCount := planEdges (T:=T) Here
    let setup := prepareRootBook X gate pad A.localName A.incident A.lanes
    let owners := mountFirstOwners X gate pad A.source B live A.keys srcInj
    let fs := trueFrames X gate pad A.localName
    let bk := frameKeys fs
    let cmds := owners.result.order.map (expectedRootCommand X pad edgeCount A.codeWidth fit)
    let eval := runRows X.hf F X.positive B (visitFramesClock fs).result cmds
    let actual := runPhysicalExterior X (withCanonicalRootWriter X gate pad A M) Rtn layout retire B head
    ∃ ans, actual=
      ⟨(ans,B),setup.steps+owners.steps+
        (3+(owners.result.raw.map (fun u=>(writeRootOwner A.codeWidth bk.result fs u).steps+7)).sum)+
        (4*N0+2)+eval.steps+13⟩ ∧
      F.decode ans=(sourceBlueprint sel Ext X.hf).program.run Ext := by
  let F := T.frame (Here).reached
  let edges := planEdges (T:=T) Here
  obtain ⟨ans,fee,law⟩ := metered_root_stop_uses_each_actual_producer_once X gate pad A basePos
    nameInj srcInj gateWidth edges hb fit F B live
  refine ⟨ans,?_ ,law.trans (true_source_stops_on_same_host T Here stop)⟩
  rw [physical_root_stop_runs_exact_paid_provider X gate pad A M Rtn layout retire B head stop]
  change (⟨((meteredRootStop X gate pad A F B).result,B),(meteredRootStop X gate pad A F B).steps⟩ :
    Meter (Block F ell×Bank))=_
  rw [fee]

#print axioms physical_root_stop_runs_exact_paid_provider
#print axioms same_original_stopped_run_charges_both_root_producers
end
end J6R68CanonicalRootWriter

