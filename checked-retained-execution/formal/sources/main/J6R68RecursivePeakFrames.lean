import J6R66BootPeakMount
import J6R50PeakStartPrecision

/-! Matrix-algebra frame bytes in the actual directory stack. Each
published occurrence owns one selected frame list, not one frame
list per Page row. If two occurrences alias frame words, counting
both selected record views is conservative. -/
namespace J6R68.RecursivePeak
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R50SourceProducer J6R24MeteredRecursion J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R51Online J6R50Peak J6R66.BootPeak J6R49LiveBits
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3950
set_option maxHeartbeats 12500000
set_option Elab.async false

theorem exact_record_frame_selected_bits {f : ℤ[X]} {prec : ℕ}
    (shape : FrameShape f prec) (hf : f.Monic) :
    frameWordsBits shape=prec+f.natDegree*shape.p := by
  have len : shape.old.length=f.natDegree :=
    J6R24MeteredRecursion.Frame.natDegree hf
      ⟨shape.pPos,shape.old,shape.degreePos,shape.algebra⟩
  unfold frameWordsBits
  rw [shape.birth.size,bitSize_exact _ _ _ (fun w : A1R10.Word shape.p=>w.property),len]

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "P" => (@Plan f ell s sel)
variable (M : OnlineMachine T key prec tw bw page q)

def frameSlope : ℕ := prec+f.natDegree*absolutePrecision s r.edges r.prec

theorem actual_birth_frame_fits_initial_precision_scale
    (p : Path sel r c) (w : (P).Slot c) :
    frameWordsBits (borns M p w).job.expected.shape≤frameSlope (prec:=prec) (s:=s) (r:=r) := by
  let birth := borns M p w
  have hP := absolute_inherited_precision_cap cfg sel T.rootStable (.step p w)
  change ((P).child c w).prec≤absolutePrecision s r.edges r.prec at hP
  change frameWordsBits birth.shape≤_
  rw [exact_record_frame_selected_bits birth.shape hf,birth.actualPrec]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hP) _

theorem actual_live_frame_stack_is_bounded (B : PageBank f ell key prec tw bw page)
    (p : Path sel r c) :
    bankFrameBits (stackBank (borns M) B p)≤
      bankFrameBits B+pathLimit s C*frameSlope (prec:=prec) (s:=s) (r:=r) := by
  let cap := frameSlope (prec:=prec) (s:=s) (r:=r)
  have one :
      bankFrameBits (stackBank (borns M) B p)≤bankFrameBits B+moves p*cap := by
    induction p with
    | root => exact Nat.le_add_right _ _
    | step parent w ih =>
      let birth := borns M parent w
      change frameWordsBits birth.job.expected.shape+bankFrameBits (stackBank (borns M) B parent)≤
        bankFrameBits B+(moves parent+1)*cap
      have here : frameWordsBits birth.job.expected.shape≤cap :=
        actual_birth_frame_fits_initial_precision_scale M parent w
      rw [Nat.add_mul,Nat.one_mul]
      calc
        _ ≤ cap+(bankFrameBits B+moves parent*cap) := Nat.add_le_add here ih
        _ = bankFrameBits B+(moves parent*cap+cap) := by
          rw [Nat.add_left_comm cap, Nat.add_comm cap (moves parent*cap)]
  exact one.trans (Nat.add_le_add_left (Nat.mul_le_mul_right cap
    (actual_ancestry_moves_any_start cfg sel T.rootStable p)) _)

#print axioms exact_record_frame_selected_bits
#print axioms actual_birth_frame_fits_initial_precision_scale
#print axioms actual_live_frame_stack_is_bounded
end
end J6R68.RecursivePeak
