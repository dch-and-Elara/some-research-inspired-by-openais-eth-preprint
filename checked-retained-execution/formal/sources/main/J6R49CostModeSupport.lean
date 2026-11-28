import J6R48DFSModeDrain
import J6R17ModeTapeDispatch

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8500000

/-! Pay for sparse mode support as the halt-driven cursor emits each
literal vector. The support list, not a typed NativeMenu lookup, is handed
to the executable continuation. This step does not itself create children. -/
namespace J6R49Cost
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply J6R48DFS

variable {q n : ℕ} {A : Type*}

def supportUpdate (a : ℕ) (rawModes : List (RawMode q))
    (step : A→List (RawMode q×Word q)→Meter A)
    (acc : A) (raw : List (Word q)) : Meter A :=
  let support := emitSupport a rawModes raw
  match support.result with
  | none => ⟨acc,support.steps+2⟩
  | some sparsity =>
    let out := step acc sparsity
    ⟨out.result,support.steps+out.steps+2⟩

theorem support_update_exact (a : ℕ) (rawModes : List (RawMode q))
    (step : A→List (RawMode q×Word q)→Meter A) (acc : A) (raw : List (Word q))
    (len : rawModes.length=raw.length) :
    let out := supportUpdate a rawModes step acc raw
    let expected := step acc (supportSpec rawModes raw)
    out.result=expected.result ∧ out.steps=expected.steps+(rawModes.length*dispatchStride a q+6) := by
  obtain ⟨v,hc⟩ := emitSupport_exact a rawModes raw len
  dsimp only
  unfold supportUpdate
  dsimp only
  rw [v]
  refine ⟨rfl,?_⟩
  dsimp only
  rw [hc]
  ring

theorem support_stream_fold_paid (a : ℕ) (rawModes : List (RawMode q))
    (step : A→List (RawMode q×Word q)→Meter A) (xs : List (List ℕ)) (acc : A)
    (lengths : ∀ v∈xs,v.length=rawModes.length) :
    let paid := foldExpected (supportUpdate a rawModes step) xs acc
    let model := foldExpected (fun x raw=>step x (supportSpec rawModes raw)) xs acc
    paid.result=model.result ∧ paid.steps=model.steps+xs.length*(rawModes.length*dispatchStride a q+6) := by
  induction xs generalizing acc with
  | nil => simp [foldExpected]
  | cons v vs ih =>
    have len : rawModes.length=(v.map (word (q:=q))).length := by
      rw [List.length_map]
      exact (lengths v List.mem_cons_self).symm
    obtain ⟨h0,h1⟩ := support_update_exact a rawModes step acc (v.map word) len
    have hT := ih (step acc (supportSpec rawModes (v.map word))).result
      (fun y hy=>lengths y (List.mem_cons_of_mem _ hy))
    simp only [foldExpected,h0,h1,hT.1,hT.2,List.length_cons]
    constructor
    · trivial
    · ring

theorem halt_driven_support_charge (a : ℕ) (rawModes : List (RawMode q))
    (step : A→List (RawMode q×Word q)→Meter A) (P : Pending q n)
    (xs : List (List ℕ)) (run : Runs n P.state xs (.ascend []))
    (lengths : ∀ v∈xs,v.length=rawModes.length) (acc : A) (fee : ℕ) :
    let out := modeDrain (supportUpdate a rawModes step) P acc fee
    let ref := foldExpected (fun x raw=>step x (supportSpec rawModes raw)) xs acc
    out.result=(ref.result,true) ∧
      out.steps≤fee+ref.steps+xs.length*(rawModes.length*dispatchStride a q+6)+
        (xs.length+1)*delayCap q n := by
  obtain ⟨value,time⟩ := halt_driven_fold_exact P xs run (supportUpdate a rawModes step) acc fee
  obtain ⟨result,steps⟩ := support_stream_fold_paid a rawModes step xs acc lengths
  exact ⟨by rw [value,result],by simpa only [steps,Nat.add_assoc] using time⟩

#print axioms supportUpdate
#print axioms support_update_exact
#print axioms support_stream_fold_paid
#print axioms halt_driven_support_charge
end J6R49Cost

