import J6R68CanonicalRootWriterOrder
import J6R52TerminalMixed

/-! Whole raw exterior writer once the measured chart is available.
The input is the genuine encoded owner roster, not an array of
precomputed Gate/Page commands. This layer specifies the fee on success
and never assumes any cap on the two input producers. -/
namespace J6R68CanonicalRootWriter
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J6R36ChildFramedRoute J6R53OldOwner J6R50Leaf J6R52Terminal J6R53TerminalGate
open J6R27OriginalGate J6R24MeteredRecursion J6R33StatefulArithmeticPage J6R62Leaf

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7000000
set_option maxRecDepth 4000
set_option Elab.async false

variable {w own g key prec page : ℕ}

def decideRootSource (b : ℕ) (book : List (Word w)) (frames : List (FramedEdge w own key prec page))
    (name : Word own) (data : OwnerData g key prec page) : Meter (Option (ReadCmd key page)) :=
  match data.gateCode with
  | some op => compileSavedGate b book frames name op
  | none =>
    match data.origin.pageKey with
    | some pg => compileFreshOne data.origin.stamp.creator book frames pg
    | none => ⟨none,3⟩

def writeRootOwner (b : ℕ) (book : List (Word w)) (frames : List (FramedEdge w own key prec page))
    (r : RefRow own (OwnerData g key prec page)) : Meter (Option (ReadCmd key page)) :=
  let name := copyFixed r.address
  let data := copyOwnerData r.payload
  let out := decideRootSource b book frames name.result data.result
  ⟨out.result,name.steps+data.steps+out.steps+5⟩

theorem root_owner_write_exact_cost (b : ℕ) (book : List (Word w))
    (frames : List (FramedEdge w own key prec page)) (r : RefRow own (OwnerData g key prec page)) :
    let out := decideRootSource b book frames r.address r.payload
    writeRootOwner b book frames r=
      ⟨out.result,(3*own+1)+ownerDataFee r.payload+out.steps+5⟩ := by
  simp only [writeRootOwner,copy_fixed_exact,copy_owner_data_exact]

def writeRootRows (b : ℕ) (book : List (Word w)) (frames : List (FramedEdge w own key prec page))
    (rows : RawRoster own g key prec page) : Meter (Option (List (ReadCmd key page))) :=
  gatherOptions 1 (writeRootOwner b book frames) rows

variable {f : ℤ[X]} {ell p tw bw : ℕ}

def runRootWriter (b : ℕ) (hf : f.Monic) (F : Frame f p) (pos : 0<ell)
    (B : PageBank f ell key prec tw bw page)
    (setup : Meter (Option (List (FramedEdge w own key prec page) × List (Word w))))
    (owners : Meter (RawRoster own g key prec page)) : Meter (Option (Block F ell)) :=
  match setup.result with
  | none => ⟨none,setup.steps+3⟩
  | some (fs,book) =>
    let cmds := writeRootRows b book fs owners.result
    match cmds.result with
    | none=>⟨none,setup.steps+owners.steps+cmds.steps+6⟩
    | some data=>
      let clock := visitFramesClock fs
      let out := runRows hf F pos B clock.result data
      ⟨some out.result,setup.steps+owners.steps+cmds.steps+clock.steps+out.steps+9⟩

theorem root_writer_uses_one_chart_and_exact_meter (b : ℕ) (hf : f.Monic) (F : Frame f p) (pos : 0<ell)
    (B : PageBank f ell key prec tw bw page)
    (setup : Meter (Option (List (FramedEdge w own key prec page) × List (Word w))))
    (owners : Meter (RawRoster own g key prec page))
    (fs : List (FramedEdge w own key prec page)) (book : List (Word w))
    (ready : setup.result=some (fs,book)) (data : List (ReadCmd key page))
    (built : (writeRootRows b book fs owners.result).result=some data) :
    let clock := visitFramesClock fs
    let out := runRows hf F pos B clock.result data
    runRootWriter b hf F pos B setup owners=
      ⟨some out.result,setup.steps+owners.steps+
        (3+(owners.result.map (fun u=>(writeRootOwner b book fs u).steps+7)).sum)+clock.steps+out.steps+9⟩ := by
  simp only [runRootWriter,ready,built]
  rw [show (writeRootRows b book fs owners.result).steps=
    3+(owners.result.map (fun u=>(writeRootOwner b book fs u).steps+7)).sum by
      unfold writeRootRows
      rw [actual_gather_step_list]]

#print axioms root_owner_write_exact_cost
#print axioms runRootWriter
#print axioms root_writer_uses_one_chart_and_exact_meter
end J6R68CanonicalRootWriter

