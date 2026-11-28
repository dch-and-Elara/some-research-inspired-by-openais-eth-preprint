import J6R58LeafScaleNoUniform
import J6R57LeafCapAttached

/-! The R51 legal terminal chart does not certify absence of off-roster
resident records. This lift preserves all checked terminal charts and
inflates the *same* R57 leaf prefactor at a matched generated row. -/
namespace J6R58LeafScale
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
open J6R48DFS J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R57LeafCap
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 46000000
set_option maxRecDepth 4700

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
variable (spare : ∀ {v : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
  (site : StoredSite P v key prec tw bw (pageKeyWidth m+pad)),
    ResidentPort (data site).own site.birth.port)

def paddedLeafFamily (len : ℕ) {v : Ticket sel ext}
    (site : StoredSite P v key prec tw bw pg) : ResidentLeafData site :=
  padLeafData site (data site) (spare site) len

theorem actual_terminal_chart_ignores_off_roster_lines
    (chart : LoopCharts X pad M basePos data)
    (unused : ∀ {v : Ticket sel ext} (site : StoredSite P v key prec tw bw pg),
      (spare site).address∉(data site).roster) (len : ℕ) :
    LoopCharts X pad M basePos (paddedLeafFamily X pad data spare len) := by
  intro c par w stop pos
  let site := sourceState M par w
  obtain ⟨name,names,law⟩ := chart par w stop pos
  refine ⟨name,names,?_⟩
  intro vertex
  have miss : name vertex≠(spare site).address := by
    intro h
    have present : name vertex∈(data site).roster := by
      rw [names]
      exact List.mem_map.mpr ⟨vertex,vertexList_complete _ vertex,rfl⟩
    exact unused site (h ▸ present)
  exact unused_resident_lines_keep_source_command _ (name vertex) (spare site) miss len
    (data site).lines (data site).table (law vertex)

theorem actual_literalLeafScaleAt_unbounded_in_old_chart_ABI
    (chart : LoopCharts X pad M basePos data)
    (unused : ∀ {v : Ticket sel ext} (site : StoredSite P v key prec tw bw pg),
      (spare site).address∉(data site).roster)
    (initial : L) {c : Call (PhysicalHost f ell)}
    (par : Path sel ext c) (w : (Plan sel).Slot c)
    (positive : 0<(par.ticket w).child.edges)
    (vertex : (par.ticket w).child.host.Row⊕(par.ticket w).child.host.Col)
    (id : J6R15ModeCost.Word key) (pgId : J6R15ModeCost.Word pg) (ticks : ℕ)
    (wires : List WireRead) (owner : J6R15ModeCost.Word (data (sourceState M par w)).own)
    (used : let site := sourceState M par w
      let D := sourceLeafTape X pad (machineInputs X pad M) basePos (Path.step par w)
        (actualEdgeOrder P (par.ticket w) site.birth.native.physical)
      ((vertex,PageReadCode.generated (edges:=(par.ticket w).child.edges) id pgId ticks wires),owner)∈
        D.rows.zip (data site).roster) (bound : ℕ) :
    let next : ∀ {v : Ticket sel ext} (site : StoredSite P v key prec tw bw pg), ResidentLeafData site :=
      fun {_} site=>paddedLeafFamily X pad data spare (bound+1) site
    LoopCharts X pad M basePos next ∧
      bound<literalLeafScaleAt X pad M basePos rootOrd next initial (Path.step par w) := by
  let site := sourceState M par w
  let path := Path.step par w
  let F := P.frame path.reached
  let B := stackBank (borns M) initial path
  let D := sourceLeafTape X pad (machineInputs X pad M) basePos path
    (actualEdgeOrder P (par.ticket w) site.birth.native.physical)
  have p : owner∈(data site).roster := (List.of_mem_zip used).2
  have miss : owner≠(spare site).address := fun eq=>unused site (eq ▸ p)
  exact ⟨actual_terminal_chart_ignores_off_roster_lines X pad M basePos data spare chart unused _,
    actual_stored_prefactor_unbounded_at_fixed_dimensions site (data site) F B D positive
      (spare site) owner miss vertex id pgId ticks wires used bound⟩

#print axioms paddedLeafFamily
#print axioms actual_terminal_chart_ignores_off_roster_lines
#print axioms actual_literalLeafScaleAt_unbounded_in_old_chart_ABI
end
end J6R58LeafScale
