import J6R51LeafBind
import J6R51OnlineCore

/-! Use the route from the born occurrence actually passed to the
demand driver. No externally chosen optional pad or prebuilt whole
InputFamily is necessary to configure the terminal fields. -/
namespace J6R51Leaf
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
open J6R50Leaf J6R50SourceProducer J6R51Online
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 45000000
set_option maxRecDepth 4400

noncomputable section
variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {V : Type} [Fintype V]
variable {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {q ro co d edgew tc tj key prec tw bw rate : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {P : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (pad : ℕ)
local notation "ext" => exteriorChild G ell X.centre X.sample X.group
local notation "pg" => pageKeyWidth m+pad
local notation "SP" => printedParams (f:=f) (ell:=ell) s
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]

variable (M : OnlineMachine P key prec tw bw (pageKeyWidth m+pad) rate)

def machineInputs : InputFamily P key prec tw bw pg :=
  fun p w=>(sourceState M p w).input

def replaceTerminalFields (basePos : 0<base)
    (rootOrd : Fin (ext).edges≃(ext).host.Edge)
    (data : ∀ {v : Ticket sel ext} (site : StoredSite P v key prec tw bw pg),ResidentLeafData site) :
    OnlineMachine P key prec tw bw pg rate :=
  { M with
    leafRoot := fun stop=>sourceRootTerminal X pad (machineInputs X pad M) basePos stop rootOrd
    leafAfter := fun p w site stop=>sourceStoredTerminal X pad (machineInputs X pad M)
      basePos p w site (fun _=>data site) stop }

theorem replacement_keeps_actual_source_state (basePos : 0<base)
    (rootOrd : Fin (ext).edges≃(ext).host.Edge)
    (data : ∀ {v : Ticket sel ext} (site : StoredSite P v key prec tw bw pg),ResidentLeafData site) :
    ∀ {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (w : (Plan sel).Slot c),
      sourceState (replaceTerminalFields X pad M basePos rootOrd data) p w=sourceState M p w := by
  intro c p
  induction p with
  | root => intro w; rfl
  | step p j ih =>
    intro w
    rw [sourceState,sourceState,ih j]
    all_goals rfl

theorem same_supplied_source_birth (basePos : 0<base)
    (rootOrd : Fin (ext).edges≃(ext).host.Edge)
    (data : ∀ {v : Ticket sel ext} (site : StoredSite P v key prec tw bw pg),ResidentLeafData site)
    {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (w : (Plan sel).Slot c) :
    borns (replaceTerminalFields X pad M basePos rootOrd data) p w=compileFamily (machineInputs X pad M) p w :=
  congrArg StoredSite.birth (replacement_keeps_actual_source_state X pad M basePos rootOrd data p w)

theorem actually_connected_leaf_decodes (basePos : 0<base)
    (rootOrd : Fin (ext).edges≃(ext).host.Edge)
    (data : ∀ {v : Ticket sel ext} (site : StoredSite P v key prec tw bw pg),ResidentLeafData site)
    {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (w : (Plan sel).Slot c)
    (stop : ((Plan sel).child c w).edges≤(SP).cutoff) (B : PageBank f ell key prec tw bw pg)
    (alive : opened (borns M) (IsLive (X.seed pad)) (Path.step p w) B)
    (name : Vertex ((Plan sel).child c w)→J6R15ModeCost.Word (data (sourceState M p w)).own)
    (names : (data (sourceState M p w)).roster=(vertexList ((Plan sel).child c w).host).map name)
    (validation : ∀ u : Vertex ((Plan sel).child c w),
      SourceCommand ((Plan sel).child c w).edges
        (fun j => childKey P (p.ticket w) (sourceState M p w).birth.native.physical
          (actualEdgeOrder P (p.ticket w) (sourceState M p w).birth.native.physical j))
        (data (sourceState M p w)).lines (data (sourceState M p w)).table (name u)
        (sourceLeafRow X pad (machineInputs X pad M) basePos (Path.step p w)
          (actualEdgeOrder P (p.ticket w) (sourceState M p w).birth.native.physical) u).code) :
    let R := replaceTerminalFields X pad M basePos rootOrd data
    let F := P.frame (Path.step p w).reached
    F.decode (R.leafAfter p w (sourceState R p w) stop B).result=
      (sourceBlueprint sel ext X.hf).program.run ((Plan sel).child c w) := by
  dsimp only
  rw [replacement_keeps_actual_source_state X pad M basePos rootOrd data p w]
  change (P.frame (Path.step p w).reached).decode
    (sourceStoredTerminal X pad (machineInputs X pad M) basePos p w (sourceState M p w)
      (fun _=>data (sourceState M p w)) stop B).result=_
  by_cases e : ((Plan sel).child c w).edges=0
  · exact (source_stored_empty_is_old X pad (machineInputs X pad M) basePos p w
      (sourceState M p w) (fun _=>data (sourceState M p w)) stop e B alive).2
  · obtain ⟨_,value,_,same,correct⟩ := source_stored_positive_exact X pad (machineInputs X pad M)
      basePos p w (sourceState M p w) rfl (fun _=>data (sourceState M p w)) stop
      (Nat.pos_of_ne_zero e) B alive name names validation
    rw [same]
    exact correct

#print axioms replacement_keeps_actual_source_state
#print axioms same_supplied_source_birth
#print axioms actually_connected_leaf_decodes
end
end J6R51Leaf
