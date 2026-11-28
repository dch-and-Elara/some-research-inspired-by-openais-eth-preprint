import J6R82LeafTimeRows

/-! Same-path stopped-leaf prices. The printed source exponent is unchanged.
The scalar uses actual encoded widths; these are not inferred from mere
value-equivalence of an arbitrary replacement chart. -/
namespace J6R82LeafTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Peak J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
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
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
local notation "deg" => (4*Nat.clog 2 s)
local notation "ch" => (p.ticket w).child

variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
variable (gateWidth : gate.created.val=base)
variable (A : OwnerTerminalInput X p w (sourceState M p w))

def stoppedReaderCoefficient (body arity significant directory : ℕ) : ℕ :=
  (vertexCount (ext).host+4*(C*s))*
    stoppedRowPrefix s C ell key prec tw bw (pageKeyWidth m+pad) body arity significant directory

include boot gateWidth in
theorem actual_ordered_leaf_reader_price
    (B : Bank) (geo : StoppedReadGeometry X M p w B)
    {body arity significant directory : ℕ}
    (W : StoppedReadWidths X M p w B A body arity significant directory)
    (older : List Cmd) (compiled : (oldCompiler X p w (sourceState M p w) A).result=some older) :
    positiveReadBill X p w (sourceState M p w) older B≤
      stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant directory*2^(6*leafH s) := by
  let Y := sourceState M p w
  let rows := older++(trueFreshPages Y).map (freshWord Y)
  let price := stoppedRowPrefix s C ell key prec tw bw (pageKeyWidth m+pad) body arity significant directory
  let power := 2^(6*leafH s)
  have census := (actual_terminal_census_and_native_width X p w Y A older compiled).2.2.1
  have all : ∀ cmd ∈ rows, readCmdFee B deg (ch).prec (ch).edges cmd≤power*price := by
    intro cmd h
    rcases List.mem_append.mp h with old|current
    · obtain ⟨u,hit⟩ := actual_ordered_old_command_has_owner_producer X M p w A older compiled cmd old
      exact actual_retained_row_has_uniform_price X M p w gate boot gateWidth B A geo W u cmd hit
    · obtain ⟨k,_,rfl⟩ := List.mem_map.mp current
      exact actual_fresh_row_has_uniform_price X M p w B A geo W k
  unfold positiveReadBill cmdBill
  exact (sum_map_cap rows (readCmdFee B deg (ch).prec (ch).edges) (power*price) all).trans
    ((Nat.mul_le_mul_right _ census).trans_eq (by
      change (vertexCount (ext).host+4*(C*s))*(power*price)=
        (vertexCount (ext).host+4*(C*s))*price*power
      ring))

include boot gateWidth in
theorem actual_stacked_ordered_leaf_reader_price
    (initial : Bank) (first : IsLive (X.seed pad) initial) (legal : ReadyOnStack (borns M) initial)
    (hn : native≤m) (hs : s=physicalSize m native) (baseFit : base≤C*s)
    {body arity significant : ℕ}
    (enc : ActualEncodingFits (stackBank (borns M) initial (.step p w)) significant)
    (frameFit : observedFrameWidth A.saved.rows≤body)
    (gateFit : observedGateWidth A.roster.raw≤arity)
    (older : List Cmd) (compiled : (oldCompiler X p w (sourceState M p w) A).result=some older) :
    positiveReadBill X p w (sourceState M p w) older (stackBank (borns M) initial (.step p w))≤
      stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
        (initial.records.length+J6R16ModeCost.pathLimit s C)*2^(6*leafH s) := by
  let walk := Path.step p w
  let B := stackBank (borns M) initial walk
  have used : opened (borns M) (IsLive (X.seed pad)) walk B :=
    stack_is_opened (borns M) initial (IsLive (X.seed pad)) (live_monotone (X.seed pad))
      first legal walk
  have rootHere := opened_keeps_root X pad (borns M) walk B used
  have count := (stack_directory_size (borns M) initial walk).2
  have isSmall := actual_ancestry_moves_any_start cfg sel T.rootStable walk
  exact actual_ordered_leaf_reader_price X M p w gate boot gateWidth A B
    ⟨hn,hs,baseFit,rootHere,used⟩
    ⟨frameFit,gateFit,enc,count.trans_le (Nat.add_le_add_left isSmall _)⟩ older compiled

#print axioms actual_ordered_leaf_reader_price
#print axioms actual_stacked_ordered_leaf_reader_price
end
end J6R82LeafTime