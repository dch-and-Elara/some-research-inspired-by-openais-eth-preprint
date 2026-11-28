import J6R68ActiveInputsSweepSetup
import J6R66ActiveRun

/-! The two actual R66 entrance shapes share one entering-call setup.
A published descendant borrows its real current head; the marked
exterior keeps the actually supplied entrance reader. -/
namespace J6R68ActiveInputs.Sweep
open scoped Polynomial
open Polynomial AOracleMachineTime J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6R26DescriptorTree J6R49DFS
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer J6R51Online
open J6R58ActivePrep J6R62ActivePrep J6R63Active J6R64Active J6R66Active

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 19000000
set_option maxRecDepth 3650
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Here" => (Path.root : Path sel r r)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

structure MountedChart (T : Prepared cfg sel r hf) where
  count : ℕ
  width : count≤2^f.natDegree
  table : MaskTable f.natDegree count width
  covers : ∀ {x : Call (PhysicalHost f ell)} (_p : Path sel r x) (_ : (S).cutoff<x.edges),
    physicalProbeCount f ell s x≤count

def rootPrepare (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (owner : OwnsHeader E.header B) (on : (S).cutoff<r.edges) :
    Meter (Schedule sel (readyAtPath T Here on) T.bank q) :=
  let taper := actual_path_taper T Here on
  let header := E.inherit B owner
  let layout := E.layout B owner on
  prepare M.modeWidth (F.fit Here on) taper.1 taper.2 hf chart.table (chart.covers Here on) header layout

def afterPrepare (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (p : Path sel r c) (w : (P).Slot c)
    (X : StoredSite T (p.ticket w) key prec tw bw page) (B : L)
    (owner : OwnsHeader X.birth.job.entry.result B)
    (on : (S).cutoff<((P).child c w).edges) :
    Meter (Schedule sel (readyAtPath T (.step p w) on) T.bank q) :=
  let walk := Path.step p w
  let taper := actual_path_taper T walk on
  let header := readIncoming X B owner
  let layout := F.layout p w X on
  prepare M.modeWidth (F.fit walk on) taper.1 taper.2 hf chart.table (chart.covers walk on) header layout

theorem actual_root_prepares_stock_from_its_one_entrance_read
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (owner : OwnsHeader E.header B) (on : (S).cutoff<r.edges) :
    let header := E.inherit B owner
    let stock := prepareStockFromHeader (s:=s) M.modeWidth header.result
    let D := rootPrepare M F chart E B owner on
    D.result.stock=stock.result ∧
    D.steps=header.steps+(E.layout B owner on).steps+(2*cw+4*q+5)+stock.steps+4 := by
  have taper := actual_path_taper T Here on
  have receipt := prepare_uses_captured_inputs_once (bank:=T.bank)
    M.modeWidth (F.fit Here on) taper.1 taper.2 hf chart.table (chart.covers Here on)
    (E.inherit B owner) (E.layout B owner on)
  exact ⟨receipt.1,receipt.2.2⟩

theorem actual_descendant_prepares_stock_from_its_one_live_head
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (p : Path sel r c) (w : (P).Slot c)
    (X : StoredSite T (p.ticket w) key prec tw bw page) (B : L)
    (owner : OwnsHeader X.birth.job.entry.result B)
    (on : (S).cutoff<((P).child c w).edges) :
    let header := readIncoming X B owner
    let stock := prepareStockFromHeader (s:=s) M.modeWidth header.result
    let D := afterPrepare M F chart p w X B owner on
    D.result.stock=stock.result ∧
    D.steps=(callReadFee prec X.birth.edge X.birth.dep X.birth.job.offset+5)+
      (F.layout p w X on).steps+(2*cw+4*q+5)+stock.steps+4 := by
  let path := Path.step p w
  have taper := actual_path_taper T path on
  have receipt := prepare_uses_captured_inputs_once (bank:=T.bank) M.modeWidth (F.fit path on)
    taper.1 taper.2 hf chart.table (chart.covers path on) (readIncoming X B owner) (F.layout p w X on)
  refine ⟨receipt.1,?_⟩
  dsimp only
  rw [show (afterPrepare M F chart p w X B owner on).steps=_ from receipt.2.2]
  rw [(incoming_words_from_published_head X B owner).2.2]

theorem real_stock_setup_independent_of_directory_tail
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (p : Path sel r c) (w : (P).Slot c)
    (X : StoredSite T (p.ticket w) key prec tw bw page) (B R : L)
    (atB : OwnsHeader X.birth.job.entry.result B) (atR : OwnsHeader X.birth.job.entry.result R)
    (on : (S).cutoff<((P).child c w).edges) :
    afterPrepare M F chart p w X B atB on=afterPrepare M F chart p w X R atR on := by
  unfold afterPrepare
  dsimp only
  rw [live_incoming_meter_independent_of_tail X B R atB atR]
end

#print axioms actual_root_prepares_stock_from_its_one_entrance_read
#print axioms actual_descendant_prepares_stock_from_its_one_live_head
#print axioms real_stock_setup_independent_of_directory_tail
end J6R68ActiveInputs.Sweep
