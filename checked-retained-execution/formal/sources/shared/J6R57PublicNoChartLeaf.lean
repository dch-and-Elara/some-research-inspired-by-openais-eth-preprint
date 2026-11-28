import J6R54TerminalBootPath
import J6R51LeafWhole

/-! The paid owner terminal is a separate source-faithful leaf recipe.
It consumes the same incoming occurrence and physical owner tapes, but
does not demand byte equality to the old proof-side `sourceLeafRow`
chosen by Classical.choice. No decoded result is a supplier field. -/
namespace J6R57Public
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths J6R54TerminalBoot J6R51Leaf J6R48DFS
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}

section Inputs
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))

structure OwnerTerminalInput where
  saved : CachedParentFrames Y.site
  headers : ParentOwnerHeaders Y.site
  roster : CompleteRoster Y.site.oldKey (parentData Y (gateHistory T (bootGates X) p))
  inj : Function.Injective Y.site.oldKey

variable (input : Meter (OwnerTerminalInput X p w Y))
variable (F : Frame f (p.ticket w).child.prec)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))

/-- Use the passed physical occurrence, not a reconstructed `sourceState`.
The caller's measured reads and the owner terminal fee are both present. -/
def executeOwnerTerminal : Meter (Option (Block F ell)) :=
  let A := input.result
  let read := meteredTerminalFromOwners Y A.saved A.headers.raw A.roster.raw
    (p.ticket w).child.edges F B
  ⟨read.result,input.steps+read.steps+4⟩

theorem owner_terminal_is_the_metered_reader :
    let A := input.result
    let read := meteredTerminalFromOwners Y A.saved A.headers.raw A.roster.raw
      (p.ticket w).child.edges F B
    executeOwnerTerminal X p w Y input F B=⟨read.result,input.steps+read.steps+4⟩ := rfl
end Inputs

section Actual
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (input : Meter (OwnerTerminalInput X p w (sourceState M p w)))
variable (F : Frame f (p.ticket w).child.prec)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))

include boot in
theorem actual_owner_terminal_correct_without_legacy_chart
    (gateWidth : gate.created.val=base) (basePos : 0<base)
    (positive : 0<(p.ticket w).child.edges)
    (rootLive : PageBank f ell key prec tw bw (pageKeyWidth m+pad)→Prop)
    (outside : IsLive (X.seed pad) B)
    (inside : opened (borns M) rootLive (.step p w) B) :
    let out := executeOwnerTerminal X p w (sourceState M p w) input F B
    ∃ word,out.result=some word ∧
      F.decode word=reduce (p.ticket w).child.prec f ell ((p.ticket w).child.host.contract X.hf) := by
  exact actual_terminal_on_one_printed_boot X M gate boot p w gateWidth
    input.result.saved input.result.headers input.result.roster input.result.inj basePos
    positive (Nat.lt_two_pow_self (n:=(p.ticket w).child.edges)).le rootLive B outside inside F
end Actual

section ChartBoundary
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (data : ∀ {v : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
  (site : StoredSite T v key prec tw bw (pageKeyWidth m+pad)),ResidentLeafData site)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)

/- The legacy chart depends on the actual resident records. Merely
retaining the same graph and live bank cannot fix an empty roster. -/
include p in
theorem an_empty_roster_cannot_supply_the_legacy_chart
    (basePos : 0<base)
    (stop : ((Plan sel).child c w).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (positive : 0<((Plan sel).child c w).edges)
    (v : ((Plan sel).child c w).host.Row ⊕ ((Plan sel).child c w).host.Col) :
    ¬ LoopCharts X pad M basePos (fun site=>{ data site with roster := [] }) := by
  intro H
  obtain ⟨name,keys,_⟩ := H p w stop positive
  change []=(vertexList ((Plan sel).child c w).host).map name at keys
  have member : name v∈(vertexList ((Plan sel).child c w).host).map name :=
    List.mem_map.mpr ⟨v,vertexList_complete _ v,rfl⟩
  rw [←keys] at member
  simp at member
end ChartBoundary

#print axioms executeOwnerTerminal
#print axioms owner_terminal_is_the_metered_reader
#print axioms actual_owner_terminal_correct_without_legacy_chart
#print axioms an_empty_roster_cannot_supply_the_legacy_chart
end
end J6R57Public

