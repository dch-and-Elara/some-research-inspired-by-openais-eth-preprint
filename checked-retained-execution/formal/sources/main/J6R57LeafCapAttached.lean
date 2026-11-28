import J6R57LeafCapRoster
import J6R51LeafWhole
import J6R51OnlineFeeDefs

/-! Bind the structural cap to the readLeaf used by the actual cached
occurrence ledger. The selected leaf fields are the real R51 terminal
installation. No leaf-wide time bound is a premise. -/
namespace J6R57LeafCap
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
open J6R48DFS J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 47000000
set_option maxRecDepth 4800

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
local notation "pg" => (pageKeyWidth m+pad)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw pg)
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable (M : OnlineMachine P key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (rootOrd : Fin (exteriorChild G ell X.centre X.sample X.group).edges≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (data : ∀ {v : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
  (site : StoredSite P v key prec tw bw (pageKeyWidth m+pad)),ResidentLeafData site)

def literalLeafScaleAt (initial : L)
    {c : Call (PhysicalHost f ell)} (p : Path sel ext c) : ℕ := by
  cases p with
  | root =>
    let p : Path sel ext ext := .root
    let F := P.frame p.reached
    let D := sourceLeafTape X pad (machineInputs X pad M) basePos p rootOrd
    exact rawLeafScale F.words.length ell (ext).prec (ext).edges D.rows.length (prepriced D F initial) F.hp
  | step par w =>
    let site := sourceState M par w
    let path := Path.step par w
    let F := P.frame path.reached
    let B := stackBank (borns M) initial path
    let D := sourceLeafTape X pad (machineInputs X pad M) basePos path
      (actualEdgeOrder P (par.ticket w) site.birth.native.physical)
    exact storedLeafInputScale site (fun _=>data site) F B D

theorem actual_installed_readLeaf_has_printed_scale
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (initial : L) (rootLive : IsLive (X.seed pad) initial)
    (valid : ReadyOnStack (borns M) initial) (chart : LoopCharts X pad M basePos data)
    {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (stop : c.edges≤(SP).cutoff) :
    (readLeaf (replaceTerminalFields X pad M basePos rootOrd data) initial p stop).steps≤
      2^(SP).cutoff*literalLeafScaleAt X pad M basePos rootOrd data initial p := by
  cases p with
  | root =>
    let p : Path sel ext ext := .root
    let F := P.frame p.reached
    let D := sourceLeafTape X pad (machineInputs X pad M) basePos p rootOrd
    have fee := (literal_leaf_all_orders X pad (machineInputs X pad M) basePos p rootOrd initial rootLive).2
    change (runTape D X.hf F P.vPositive initial).steps≤2^(SP).cutoff*
      rawLeafScale F.words.length ell (ext).prec (ext).edges D.rows.length (prepriced D F initial) F.hp
    exact fee.trans (raw_leaf_cap_has_printed_factor _ _ _ _ _ _ _ F.hp stop)
  | step par w =>
    let R := replaceTerminalFields X pad M basePos rootOrd data
    let site := sourceState M par w
    let path := Path.step par w
    let F := P.frame path.reached
    let B := stackBank (borns M) initial path
    let ord := actualEdgeOrder P (par.ticket w) site.birth.native.physical
    let D := sourceLeafTape X pad (machineInputs X pad M) basePos path ord
    have chartFormat : opened (borns M) (IsLive (X.seed pad)) path B :=
      stack_is_opened (borns M) initial (IsLive (X.seed pad)) (live_monotone (X.seed pad))
        rootLive valid path
    have form : HasResidentFormat D B :=
      compiled_leaf_format (planEdges (T:=P) path)
        (sourceLeafRow X pad (machineInputs X pad M) basePos path ord) B chartFormat
    have costs := stored_leaf_cap_from_literal_roster site (fun _=>data site) F P.vPositive B D form
      (SP).cutoff stop (by
      intro pos
      obtain ⟨name,names,allowed⟩ := chart par w stop pos
      refine ⟨name,?_,?_⟩
      · change (data site).roster=((vertexList (par.ticket w).child.host).map
          (fun v=>(v,(sourceLeafRow X pad (machineInputs X pad M) basePos path ord v).code))).map
            (name∘Prod.fst)
        rw [List.map_map]
        exact names
      · intro x hx
        change x∈(vertexList (par.ticket w).child.host).map
          (fun v=>(v,(sourceLeafRow X pad (machineInputs X pad M) basePos path ord v).code)) at hx
        obtain ⟨v,_,rfl⟩ := List.mem_map.mp hx
        exact allowed v)
    have st : sourceState R par w=site :=
      replacement_keeps_actual_source_state X pad M basePos rootOrd data par w
    have bk : stackBank (borns R) initial path=B :=
      congrArg (fun (births : Births P key prec tw bw pg)=>stackBank births initial path)
        (wired_births_are_original X pad M basePos rootOrd data)
    change (R.leafAfter par w (sourceState R par w) stop (stackBank (borns R) initial path)).steps≤_
    rw [st,bk]
    exact costs.2

#print axioms literalLeafScaleAt
#print axioms actual_installed_readLeaf_has_printed_scale
end
end J6R57LeafCap
