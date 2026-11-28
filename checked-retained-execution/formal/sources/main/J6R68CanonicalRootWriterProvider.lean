import J6R68CanonicalRootWriterCallback
import J6R51OnlineCorrect
import J6R51OnlineFeeDefs

/-! Replace only the root stop provider of the actual online
machine. The stamped child history and all non-root providers are
unchanged. ReadLeaf consumes exactly the same metered callback. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6ActiveRun J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R67CanonicalStop J6R11Blueprint J6R49Leaf J6R51Leaf J6R34ChildPath
open J6R24MeteredRecursion J6R51Online J1PPrinted J6R10Reachable J6R30ProducedGateRegistry J6R50SourceProducer J6R48DFS

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4500
set_option Elab.async false

noncomputable section
section Generic
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "Here" => (Path.root : Path sel r r)
local notation "Machine" => (OnlineMachine T key prec tw bw page rate)
local notation "Bank" => (PageBank f ell key prec tw bw page)
local notation "RootFrame" => (T.frame (Path.root : Path sel r r).reached)

def withRootStopProvider (M : Machine) (newRoot : Bank→Meter (Block RootFrame ell)) :
    Machine :=
  { M with leafRoot:=fun _ B=>newRoot B }

theorem root_provider_preserves_all_stored_sites (M : Machine)
    (newRoot : Bank→Meter (Block RootFrame ell))
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (Plan sel).Slot c) :
    sourceState (withRootStopProvider M newRoot) p u=sourceState M p u := by
  induction p with
  | root => rfl
  | step p w ih =>
    change ((M.demand (sourceState (withRootStopProvider M newRoot) p w) u).result.advance).next=
      ((M.demand (sourceState M p w) u).result.advance).next
    rw [ih]

theorem root_provider_preserves_all_births (M : Machine) (newRoot : Bank→Meter (Block RootFrame ell)) :
    ((fun {_} p u=>borns (withRootStopProvider M newRoot) p u) : Births T key prec tw bw page)=
      (fun {_} p u=>borns M p u) := by
  funext c p u
  exact congrArg StoredSite.birth (root_provider_preserves_all_stored_sites M newRoot p u)

theorem read_leaf_root_is_the_paid_provider (M : Machine) (newRoot : Bank→Meter (Block RootFrame ell))
    (B : Bank) (stop : r.edges≤(printedParams (f:=f) (ell:=ell) s).cutoff) :
    readLeaf (withRootStopProvider M newRoot) B Here stop=newRoot B := rfl

theorem read_leaf_descendant_is_unchanged (M : Machine) (newRoot : Bank→Meter (Block RootFrame ell))
    (B : Bank) {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (Plan sel).Slot c)
    (stop : ((Plan sel).child c u).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff) :
    readLeaf (withRootStopProvider M newRoot) B (.step p u) stop=readLeaf M B (.step p u) stop := by
  change M.leafAfter p u (sourceState (withRootStopProvider M newRoot) p u) stop
    (stackBank (borns (withRootStopProvider M newRoot)) B (.step p u))=
      M.leafAfter p u (sourceState M p u) stop (stackBank (borns M) B (.step p u))
  have bankEq : stackBank (borns (withRootStopProvider M newRoot)) B (.step p u)=
      stackBank (borns M) B (.step p u) :=
    congrArg (fun x : Births T key prec tw bw page=>stackBank x B (.step p u))
      (root_provider_preserves_all_births M newRoot)
  rw [root_provider_preserves_all_stored_sites,bankEq]
end Generic

section Connected
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {plant : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) plant (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw s C rate own old : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Here" => (Path.root : Path sel
  (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group))
local notation "Machine" => (OnlineMachine T key prec tw bw Pg rate)
local notation "Bank" => (PageBank f ell key prec tw bw Pg)
variable (A : RootStopInputs X gate pad own old)

def withCanonicalRootWriter (M : Machine) : Machine :=
  withRootStopProvider M (meteredRootStop X gate pad A (T.frame (Here).reached))

variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]

theorem actual_paid_root_provider_preserves_original_leaf_agreement
    (M : Machine) (B : Bank) (live : IsLive (X.seed pad) B)
    (basePos : 0<base) (nameInj : Function.Injective A.localName)
    (srcInj : Function.Injective A.sourceName) (gateWidth : gate.created.val=base)
    (hb : 0<A.codeWidth) (fit : (Ext).edges≤2^A.codeWidth)
    (prior : LeafAgreement M B) :
    LeafAgreement (withCanonicalRootWriter X gate pad A M) B := by
  constructor
  · intro stop
    let frame := T.frame (Here).reached
    have edges : (Ext).host.edgeCount=(Ext).edges := planEdges (T:=T) Here
    obtain ⟨ans,fee,law⟩ := metered_root_stop_uses_each_actual_producer_once X gate pad A basePos
      nameInj srcInj gateWidth edges hb fit frame B live
    change frame.decode (meteredRootStop X gate pad A frame B).result=_
    rw [fee]
    exact law.trans (true_source_stops_on_same_host T Here stop)
  · intro c p u stop
    change (T.frame (Path.step p u).reached).decode
      (readLeaf (withCanonicalRootWriter X gate pad A M) B (.step p u) stop).result=_
    unfold withCanonicalRootWriter
    rw [read_leaf_descendant_is_unchanged]
    exact prior.after p u stop

end Connected
#print axioms root_provider_preserves_all_stored_sites
#print axioms root_provider_preserves_all_births
#print axioms read_leaf_root_is_the_paid_provider
#print axioms read_leaf_descendant_is_unchanged
#print axioms actual_paid_root_provider_preserves_original_leaf_agreement
end
end J6R68CanonicalRootWriter

