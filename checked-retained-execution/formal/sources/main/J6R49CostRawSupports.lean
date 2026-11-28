import J6R49CostModeSupport
import J6R25PreparedSupplyProducer

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13500000
set_option maxRecDepth 2300

/-! A literal raw tape runner: it never computes the typed menu or a
completed list of tuples. The mathematical weighted trace is used
exclusively in the correctness and cost theorems. -/
namespace J6R49Cost
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply J6R48DFS
open scoped Polynomial
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost J1PPrinted

variable {q : ℕ} {A : Type*}

def runRawSupports (a : ℕ) (T : RawTape q) (h : RawValid T)
    (step : A→List (RawMode q×Word q)→Meter A) (acc : A) : Meter (A×Bool) :=
  let startWord := start T.weights T.precision
  match e : startWord.result with
  | .halt => ⟨(acc,false),startWord.steps+4⟩
  | .emit _ _ => ⟨(acc,false),startWord.steps+4⟩
  | .again s =>
    let p := initial_pending T h.posWidth h.posPrec h.posWeights e
    modeDrain (supportUpdate a T.modes step) (⟨s,p.1,⟨_,p.2⟩⟩ : Pending q T.weights.length)
      acc (startWord.steps+4)

theorem raw_support_runner_exact (a : ℕ) (T : RawTape q) (h : RawValid T)
    (step : A→List (RawMode q×Word q)→Meter A) (acc : A) :
    let xs := strictTuples (T.weights.map Word.val) T.precision.val
    let out := runRawSupports a T h step acc
    let model := foldExpected (fun x raw=>step x (supportSpec T.modes raw)) xs acc
    out.result=(model.result,true) ∧
    out.steps≤16*q+14+4*(T.weights.length+1)*(q+1)+4+model.steps+
      xs.length*(T.modes.length*dispatchStride a q+6)+(xs.length+1)*delayCap q T.weights.length := by
  let xs := strictTuples (T.weights.map Word.val) T.precision.val
  obtain ⟨u,hu,hRun⟩ := (stream_all_exact h.posWidth T.weights T.precision h.posWeights).2 h.posPrec.ne'
  let P : Pending q T.weights.length :=
    ⟨.enter T.weights u [],by simp [State.wellFormed,StackShape],⟨_,hRun⟩⟩
  have positive (w : ℕ) (mem : w∈T.weights.map Word.val) : 0<w := by
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp mem
    exact h.posWeights v hv
  have lengths (v : List ℕ) (hv : v∈xs) : v.length=T.modes.length := by
    have hl := ((strictTuples_exact _ _ positive).2 v |>.mp hv).1
    simpa only [List.length_map,h.sameLength] using hl
  have receipt :=
    halt_driven_support_charge a T.modes step P xs hRun lengths acc ((start T.weights T.precision).steps+4)
  have hStart := (start_exact h.posWidth T.weights T.precision).2
  unfold runRawSupports
  dsimp only
  split
  · rename_i gone
    rw [hu] at gone
    cases gone
  · rename_i _ _ gone
    rw [hu] at gone
    cases gone
  · rename_i t ht
    have e : t=.enter T.weights u [] := Pulse.again.inj (ht.symm.trans hu)
    subst t
    refine ⟨receipt.1,receipt.2.trans ?_⟩
    exact Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_right hStart _) _) _) _

#print axioms runRawSupports
#print axioms raw_support_runner_exact
end J6R49Cost

