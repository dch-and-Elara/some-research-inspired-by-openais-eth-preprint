import J6R67CanonicalStopZero
import J6R62LeafOldFormat

/-! At a successful zero-edge leaf the native compiler can emit
constant Gate or Page instructions, but cannot emit any individual
wire read. This is a structural property of the produced bytes,
not an arbitrary extensional RowAt witness. -/
namespace J6R67CanonicalStop
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths J6R54TerminalBoot J6R51Leaf J6R48DFS
open J6R48Leaf J6R57Public J6R62Leaf

set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11000000
set_option maxRecDepth 4200
set_option Elab.async false

def gateReadCount {w : ℕ} : CodeGate (Word w)→ℕ
  | .free => 0
  | .equal xs => xs.length
  | .clause xs _ => xs.length

def commandReadCount {key page : ℕ} : ReadCmd key page→ℕ
  | .gate _ op => gateReadCount op
  | .packet _ _ _ wires => wires.length

theorem no_gate_wire_without_edges {w b : ℕ}
    (source : CodeGate (Word w)) (out : CodeGate (Word b))
    (built : (compileCurrentGate b [] source).result=some out) :
    gateReadCount out=0 := by
  cases source with
  | free =>
    have E : CodeGate.free=out := Option.some.inj built
    cases E
    rfl
  | equal ports =>
    cases ports with
    | nil =>
      have E : CodeGate.equal []=out := Option.some.inj built
      cases E
      rfl
    | cons x tail =>
      simp only [compileCurrentGate,gatherOptions,findOrdinal,scanOrdinal,Option.bind_none,Option.map_none] at built
      contradiction
  | clause ports signs =>
    cases ports with
    | nil =>
      have E : CodeGate.clause [] (copyBytes signs).result=out := Option.some.inj built
      cases E
      rfl
    | cons x tail =>
      simp only [compileCurrentGate,gatherOptions,findOrdinal,scanOrdinal,Option.bind_none,Option.map_none] at built
      contradiction

theorem no_retained_gate_wire_without_frames {w W own key prec page b : ℕ}
    (owner : Word own) (source : CodeGate (Word w)) (out : ReadCmd key page)
    (got : (compileSavedGate (W:=W) (prec:=prec) b [] [] owner source).result=some out) :
    commandReadCount out=0 := by
  dsimp only [compileSavedGate] at got
  split at got
  · contradiction
  · rename_i g z
    dsimp only at got
    cases built : (compileCurrentGate (w:=W) b [] g).result with
    | none =>
      simp only [built,Option.map_none] at got
      contradiction
    | some op =>
      have same : ReadCmd.gate b op=out := by simpa only [built,Option.map_some,Option.some.injEq] using got
      rw [←same]
      exact no_gate_wire_without_edges g op built

theorem no_retained_packet_wire_without_frames {w own key prec page : ℕ}
    (owner : Word own) (origin : Origin key prec page) (out : ReadCmd key page)
    (got : (compileKeptPage (w:=w) owner origin [] []).result=some out) :
    commandReadCount out=0 := by
  cases pick : origin.pageKey with
  | none =>
    simp only [compileKeptPage,copy_origin_exact,pick] at got
    contradiction
  | some k =>
    have h : ReadCmd.packet origin.stamp.creator k 0 []=out := by
      simpa [compileKeptPage,copy_origin_exact,pick,collectRetained,requestDepth,emitWires] using got
    rw [←h]
    rfl

theorem no_fresh_packet_wire_without_frames {w own key prec page : ℕ}
    (id : Word key) (pg : Word page) (out : ReadCmd key page)
    (got : (compileFreshOne (w:=w) (own:=own) (prec:=prec) id [] [] pg).result=some out) :
    commandReadCount out=0 := by
  have h : ReadCmd.packet id pg 0 []=out := by
    simpa only [compileFreshOne,scanFresh,emitWires,copy_fixed_exact,Option.map_some,Option.some.injEq] using got
  rw [←h]
  rfl

theorem no_compiled_owner_wire_without_frames {own W w key prec page b : ℕ}
    (roster : RawRoster own w key prec page) (owner : Word own) (out : ReadCmd key page)
    (got : (compileByRoster (W:=W) b [] [] roster owner).result=some out) :
    commandReadCount out=0 := by
  cases h : (paidOwnerLookup roster owner).result with
  | none =>
    simp only [compileByRoster,h] at got
    contradiction
  | some data =>
    cases op : data.gateCode with
    | none =>
      exact no_retained_packet_wire_without_frames (w:=W) owner data.origin out
        (by simpa only [compileByRoster,compileByOwnerData,h,op] using got)
    | some g =>
      exact no_retained_gate_wire_without_frames (W:=W) (prec:=prec) owner g out
        (by simpa only [compileByRoster,compileByOwnerData,h,op] using got)

#print axioms no_gate_wire_without_edges
#print axioms no_retained_gate_wire_without_frames
#print axioms no_retained_packet_wire_without_frames
#print axioms no_fresh_packet_wire_without_frames
#print axioms no_compiled_owner_wire_without_frames

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
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
local notation "Y" => (sourceState M p w)
local notation "K" => (p.ticket w).child
local notation "Pg" => (pageKeyWidth m+pad)

theorem actual_zero_instructions_have_no_wires
    (A : OwnerTerminalInput X p w (sourceState M p w)) (zero : (K).edges=0)
    (older : List (ReadCmd key Pg)) (ok : (zeroOldCompiler X M p w A).result=some older) :
    ∀ cmd∈older++(trueFreshPages Y).map (freshWord Y),commandReadCount cmd=0 := by
  let site := sourceState M p w
  let bk := cachedBook site A.saved
  have noFrames : A.saved.rows=[] :=
    List.length_eq_zero_iff.mp ((canonical_terminal_table_censuses X p w site A).1.trans zero)
  have noKeys : bk.result=[] := by
    unfold bk cachedBook
    rw [noFrames]
    rfl
  intro cmd mem
  rcases List.mem_append.mp mem with old|fresh
  · let names := selectOwnerKeys (word (p.ticket w).groupAt.val) A.headers.raw
    let one := compileByRoster 1 bk.result A.saved.rows A.roster.raw
    obtain ⟨owner,_,built⟩ := gathered_item_was_actually_acquired 1 one names.result older ok cmd old
    unfold one at built
    rw [noFrames,noKeys] at built
    exact no_compiled_owner_wire_without_frames (W:=site.birth.port) A.roster.raw owner cmd built
  · obtain ⟨k,_,rfl⟩ := List.mem_map.mp fresh
    have built := (compile_cached_fresh_one site A.saved k).1
    change (compileFreshOne site.birth.job.identifier bk.result A.saved.rows
      (occurrencePageWord site.input k)).result=some (freshWord site k) at built
    rw [noFrames,noKeys] at built
    exact no_fresh_packet_wire_without_frames (w:=site.birth.port) (own:=site.site.ownerWidth)
      (prec:=prec) site.birth.job.identifier (occurrencePageWord site.input k) (freshWord site k) built

#print axioms actual_zero_instructions_have_no_wires
end

end J6R67CanonicalStop

