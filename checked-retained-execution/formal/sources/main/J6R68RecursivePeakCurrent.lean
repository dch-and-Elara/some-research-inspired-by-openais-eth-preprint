import J6R68RecursivePeakControl

/-! Only the destination output of one actual R62 centre preparation
is observed here. The catalogue produced by some other ordinal
executor is not included or silently substituted. -/
namespace J6R68.RecursivePeak
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits
open J6R50SourceProducer J6R51Online J6R51Peak J6R52Peak J6R52CacheWhole J6R50Peak
open J6R53PeakAddon J6R54PeakInput J6R63Active J6R64Active J6R66Active J6R62ActivePrep
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4050
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 7000000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

variable (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
variable (E : RootInputs T key prec tw bw page cw ew)
variable (B : PageBank f ell key prec tw bw page) (own : OwnsHeader E.header B)

def nativeCentreInputs (p : Path sel r c) (a : (S).cutoff<c.edges) (t : Center S c) :
    CentreWords sel (readyAtPath T p a) t q :=
  let L := liveLayoutWord M F E B own p a
  let U := actual_path_taper T p a
  (centreWords M.modeWidth (F.fit p a) U.1 U.2 (liveCallWords M E B own p).2.result
    (copyOfLayout q L.result).result (retained_layout_copy_word L.result (F.fit p a).copies).1 t).result

theorem actual_centre_tape_is_the_real_words_result
    (p : Path sel r c) (a : (S).cutoff<c.edges) (t : Center S c) :
    ((liveActiveAt M F E B own p a).result.tape t).tape.result=
      (fromWords M.modeWidth ((F.fit p a).axis t) (nativeCentreInputs M F E B own p a t)).result := by
  cases p <;> rfl

def liveCentreOutputBits (p : Path sel r c) (a : (S).cutoff<c.edges) (t : Center S c) : ℕ :=
  currentCentreProducerBits M.modeWidth (nativeCentreInputs M F E B own p a t)
    (liveLayoutWord M F E B own p a)

theorem real_live_centre_has_exact_selected_outputs
    (p : Path sel r c) (a : (S).cutoff<c.edges) (t : Center S c) :
    let A := (S).levelBits c.depth
    let tape := ((liveActiveAt M F E B own p a).result.tape t).tape.result
    liveCentreOutputBits M F E B own p a t=
      cw+q+tape.modes.length*(6*A+6*A+q+q+q)+tape.modes.length*q+q := by
  dsimp only
  rw [actual_centre_tape_is_the_real_words_result M F E B own p a t]
  exact (exact_current_native_outputs_from_same_r66_active_tape M.modeWidth
    ((F.fit p a).axis t) (nativeCentreInputs M F E B own p a t) (liveLayoutWord M F E B own p a)).2.2.2

#print axioms actual_centre_tape_is_the_real_words_result
#print axioms real_live_centre_has_exact_selected_outputs
end
end J6R68.RecursivePeak