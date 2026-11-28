import J6R62LeafActual

/-! The genuine installed terminal compiler also works at a zero-edge
successor. Use a single address bit (positive width), and use the
actual parent cache and complete owner roster, including isolated
owners. No arbitrary RowAt/leaf descriptor is selected by the runner. -/
namespace J6R67CanonicalStop
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
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
set_option maxHeartbeats 16500000
set_option maxRecDepth 4500
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
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)

local notation "Y" => (sourceState M p w)
local notation "K" => (p.ticket w).child
local notation "F" => (T.frame (Path.step p w).reached)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Bank" => (PageBank f ell key prec tw bw Pg)
local notation "Input" => (OwnerTerminalInput X p w Y)
local notation "Cmd" => (ReadCmd key Pg)

def zeroOldCompiler (A : Input) : Meter (Option (List Cmd)) :=
  compileSelectedOwners 1 (cachedBook Y A.saved) A.saved.rows A.roster.raw A.headers.raw
    (word (p.ticket w).groupAt.val)

def zeroTerminal (input : Meter (OwnerTerminalInput X p w (sourceState M p w))) (B : Bank) :
    Meter (Option (Block (T.frame (Path.step p w).reached) ell)) :=
  let A : OwnerTerminalInput X p w (sourceState M p w) := input.result
  let old := zeroOldCompiler X M p w A
  let out := @J6R53TerminalGate.joinPaidTerminal f ell s C key prec tw bw Pg cfg sel
    (exteriorChild G ell X.centre X.sample X.group) X.hf T (p.ticket w)
    (sourceState M p w) A.saved old (T.frame (Path.step p w).reached) B
  ⟨out.result,input.steps+out.steps+4⟩

theorem zero_terminal_uses_actual_paid_source
    (input : Meter (OwnerTerminalInput X p w (sourceState M p w))) (B : Bank)
    (gate : Stamp key prec)
    (boot : ExactPrintedBoot X M gate) (gateWidth : gate.created.val=base)
    (basePos : 0<base) (zero : (K).edges=0) (rootLive : Bank→Prop)
    (outside : IsLive (X.seed pad) B)
    (inside : opened (borns M) rootLive (.step p w) B) :
    ∃ word,(zeroTerminal X M p w input B).result=some word ∧
      (F).decode word=reduce (K).prec f ell ((K).host.contract X.hf) := by
  have fit : (K).edges≤2^(1:ℕ) := by rw [zero]; decide
  exact actual_terminal_on_one_printed_boot X M gate boot p w gateWidth
    input.result.saved input.result.headers input.result.roster input.result.inj basePos
    (b:=1) (by decide) fit rootLive B outside inside F

theorem zero_terminal_full_paid_program
    (input : Meter (OwnerTerminalInput X p w (sourceState M p w))) (B : Bank)
    (zero : (K).edges=0) (word : Block F ell)
    (ok : (zeroTerminal X M p w input B).result=some word) :
    let A : OwnerTerminalInput X p w (sourceState M p w) := input.result
    let old := zeroOldCompiler X M p w A
    let fresh := compileAllFresh Y A.saved
    ∃ older, old.result=some older ∧
      let cmds := older++(trueFreshPages Y).map (freshWord Y)
      let run := runRows X.hf F T.vPositive B [] cmds
      older.length=Nat.card (K).host.Row ∧ cmds.length=vertexCount (K).host ∧
      (zeroTerminal X M p w input B)=
        ⟨some run.result,input.steps+old.steps+fresh.steps+4*older.length+run.steps+20⟩ := by
  let A : OwnerTerminalInput X p w (sourceState M p w) := input.result
  let old := zeroOldCompiler X M p w A
  let fresh := compileAllFresh Y A.saved
  change (joinPaidTerminal (T:=T) (v:=p.ticket w) Y A.saved old F B).result=some word at ok
  cases cOld : old.result with
  | none =>
    dsimp only [joinPaidTerminal] at ok
    rw [cOld] at ok
    contradiction
  | some older =>
    let cmds := older++(trueFreshPages Y).map (freshWord Y)
    let clock := visitFramesClock A.saved.rows
    have hOld := (accepted_gather_census 1
      (compileByRoster 1 (cachedBook Y A.saved).result A.saved.rows A.roster.raw)
      (selectOwnerKeys (J6R15ModeCost.word (p.ticket w).groupAt.val) A.headers.raw).result older cOld).trans
      (actual_selected_owner_count X p w Y A)
    have cnt : cmds.length=vertexCount (K).host := by
      dsimp only [cmds]
      rw [List.length_append,List.length_map,hOld,actual_current_atlas_column_count X p w Y]
      rfl
    have frames : A.saved.rows.length=0 :=
      (canonical_terminal_table_censuses X p w Y A).1.trans zero
    have empty : A.saved.rows=[] := List.length_eq_zero_iff.mp frames
    have emptyClock : clock=⟨[],2⟩ := by
      unfold clock
      rw [empty]
      rfl
    have paid := measured_joined_terminal_exact (T:=T) (v:=p.ticket w) Y A.saved old F B older cOld
    change joinPaidTerminal (T:=T) (v:=p.ticket w) Y A.saved old F B=
      ⟨some (runRows X.hf F T.vPositive B clock.result cmds).result,
        old.steps+fresh.steps+(4*older.length+3)+clock.steps+
          (runRows X.hf F T.vPositive B clock.result cmds).steps+11⟩ at paid
    rw [emptyClock] at paid
    refine ⟨older,cOld,hOld,cnt,?_⟩
    unfold zeroTerminal
    dsimp only
    change (⟨(joinPaidTerminal (T:=T) (v:=p.ticket w) Y A.saved old F B).result,
      input.steps+(joinPaidTerminal (T:=T) (v:=p.ticket w) Y A.saved old F B).steps+4⟩ : Meter (Option (Block F ell)))=_
    rw [paid]
    dsimp only
    congr 1
    let fee := (runRows X.hf F T.vPositive B [] cmds).steps
    change input.steps+(old.steps+fresh.steps+(4*older.length+3)+2+fee+11)+4=
      input.steps+old.steps+fresh.steps+4*older.length+fee+20
    omega

#print axioms zeroOldCompiler
#print axioms zeroTerminal
#print axioms zero_terminal_uses_actual_paid_source
#print axioms zero_terminal_full_paid_program
end
end J6R67CanonicalStop

