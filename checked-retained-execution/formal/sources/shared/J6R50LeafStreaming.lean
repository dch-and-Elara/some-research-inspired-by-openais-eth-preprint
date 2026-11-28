import J6R50LeafNative
import J6R50LeafPatch

/-! Use the exact addressed R50 leaf compiler in the pre-existing
scoped StreamingResident. No active arithmetic, creation register,
directory operation, or fallback leaf is replaced by this adapter. -/
namespace J6R50Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12
open J6Mesh J6OrientedHost P11FullPacking P1DyadicGrid J6R24LegalLayout
open J6R10Repack J6R11Blueprint J6R11Repack J6R12Blueprint J6R21Ancestor J6R20Ancestor
open J6R14ZeroMode J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R27OriginalGate J6R9PacketScopes
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R26StablePreparedRoot
open J6R34RootAtlas J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6R30ProducedGateRegistry J6R22Active J6R35RootOrigins J6R48Leaf J6R49Leaf
open J6R9Recursive J6R10Reachable J6R24MeteredRecursion J6R21Leaf J6R16ModeCost
open J6R26DescriptorTree J6R34ChildPath J6R25PreparedSupply
open J6R49DFS
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 42000000
set_option maxRecDepth 4200

noncomputable section
variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {V : Type} [Fintype V]
variable {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {q ro co d edgew tc tj key prec tw bw own port eW dW tW zW mW rate : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {P : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (pad : ℕ)
variable (actual : InputFamily P key prec tw bw (pageKeyWidth m+pad))
local notation "ext" => exteriorChild G ell X.centre X.sample X.group
local notation "pg" => pageKeyWidth m+pad
local notation "SP" => printedParams (f:=f) (ell:=ell) s
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

def namedOnlinePatch (R : StreamingResident P key prec tw bw pg rate)
    (sameBirths :
      ((fun {_} p w=>R.births p w) : J6R33StatefulArithmeticPage.Births P key prec tw bw pg)=
      (fun {_} p w=>compileFamily actual p w))
    (sameRoot : R.rootLive=IsLive (X.seed pad))
    (basePos : 0<base)
    {c : Call (PhysicalHost f ell)} (par : Path sel ext c) (slot : (Plan sel).Slot c)
    (J : NativeJob P (par.ticket slot) port eW dW prec tW zW mW)
    (stop : ((Plan sel).child c slot).edges≤(SP).cutoff)
    (positive : 0<((Plan sel).child c slot).edges)
    (lines : List (ResidentPort own port)) (table : OriginTable own port key prec pg)
    (roster : List (J6R15ModeCost.Word own))
    (name : Vertex ((Plan sel).child c slot)→J6R15ModeCost.Word own)
    (actualNames : roster=(vertexList ((Plan sel).child c slot).host).map name)
    (validation : ∀ u : Vertex ((Plan sel).child c slot),
      SourceCommand ((Plan sel).child c slot).edges
        (fun j => childKey P (par.ticket slot) J.physical (actualEdgeOrder P (par.ticket slot) J.physical j))
        lines table (name u)
        (sourceLeafRow X pad actual basePos (Path.step par slot)
          (actualEdgeOrder P (par.ticket slot) J.physical) u).code) :
    LeafPatch R (Path.step par slot) where
  positive := positive
  attempt B :=
    let p := Path.step par slot
    let F := P.frame p.reached
    let leaf := (Plan sel).child c slot
    let book := selectedEdgeBook J.gWord J.physical.raw
    onlineLeaf X.hf F P.vPositive B leaf.edges leaf.edges book lines table roster
  exactRead B openedLive := by
    have roots := congrArg (fun live : PageBank f ell key prec tw bw pg→Prop =>
      opened (fun {_} p w=>R.births p w) live (Path.step par slot) B) sameRoot
    have birthEq := congrArg (fun birth : J6R33StatefulArithmeticPage.Births P key prec tw bw pg =>
      opened birth (IsLive (X.seed pad)) (Path.step par slot) B) sameBirths
    have actualLive : opened (compileFamily actual) (IsLive (X.seed pad)) (Path.step par slot) B :=
      Eq.mp birthEq (Eq.mp roots openedLive)
    obtain ⟨value,actualResult,which,_⟩ :=
      same_named_child_online_from_selected_book X pad actual basePos par slot J stop positive B
        actualLive lines table roster name actualNames validation
    exact ⟨value,actualResult,which.trans (P.correctAt _ (Path.step par slot).reached).symm⟩

#print axioms namedOnlinePatch
end
end J6R50Leaf
