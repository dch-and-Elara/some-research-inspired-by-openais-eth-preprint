import J6R48DFSModeDrain
import J6R16ModeCostMeter

/-! Prepare the real halt-driven cursor from the word-level start
result. Each proof of that state's future trace is in Prop, and the
state (in Type) is read directly from the actual start calculation.
The mathematical reference list is never constructed by the cursor.-/
namespace J6R49DFS
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint

set_option autoImplicit false
set_option maxRecDepth 2400
set_option maxHeartbeats 5700000

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}

abbrev tupleSpec (I : SiteTape sel d t q) :=
  strictTuples (I.modes.map modeWeight) (registerPrecision S c t)

theorem positive_tape_weights (I : SiteTape sel d t q) :
    ∀ w∈I.words,0<w.val := by
  intro w hw
  have hit : w.val∈I.words.map Word.val := List.mem_map_of_mem hw
  rw [I.weightMeaning] at hit
  obtain ⟨m,_,hm⟩ := List.mem_map.mp hit
  rw [←hm]
  exact (modeWeight_bounds m).1

theorem genuine_cursor_start (I : SiteTape sel d t q) (hq : 0<q) :
    ∃ w, (start I.words I.precision).result=.again (.enter I.words w []) ∧
      (State.enter I.words w []).wellFormed I.words.length ∧
      Runs I.words.length (.enter I.words w []) (tupleSpec I) (.ascend []) := by
  have hp : 0<I.precision.val := I.precisionMeaning ▸ register_positive d t
  obtain ⟨_,yes⟩ := stream_all_exact hq I.words I.precision (positive_tape_weights I)
  obtain ⟨w,hm,path⟩ := yes hp.ne'
  rw [I.weightMeaning,I.precisionMeaning] at path
  exact ⟨w,hm,by simp [State.wellFormed,StackShape],path⟩

theorem genuine_cursor_state (I : SiteTape sel d t q) (hq : 0<q)
    {state : State q} (actual : (start I.words I.precision).result=.again state) :
    state.wellFormed I.words.length ∧ Runs I.words.length state (tupleSpec I) (.ascend []) := by
  obtain ⟨w,emit,valid,tr⟩ := genuine_cursor_start I hq
  have e : state=.enter I.words w [] := Pulse.again.inj (actual.symm.trans emit)
  subst state
  exact ⟨valid,tr⟩

def startingCursor (I : SiteTape sel d t q) (hq : 0<q) :
    Meter (Option (Pending q I.words.length)) :=
  let z := start I.words I.precision
  match e : z.result with
  | .again st =>
    let valid := genuine_cursor_state I hq e
    ⟨some ⟨st,valid.1,⟨tupleSpec I,valid.2⟩⟩,z.steps⟩
  | .halt => ⟨none,z.steps⟩
  | .emit _ _ => ⟨none,z.steps⟩

theorem starting_cursor_exact (I : SiteTape sel d t q) (hq : 0<q) :
    ∃ Q : Pending q I.words.length, (startingCursor I hq).result=some Q ∧
      (startingCursor I hq).steps=(start I.words I.precision).steps ∧
      Runs I.words.length Q.state (tupleSpec I) (.ascend []) := by
  obtain ⟨w,a,h,tr⟩ := genuine_cursor_start I hq
  let Q : Pending q I.words.length := ⟨.enter I.words w [],h,⟨tupleSpec I,tr⟩⟩
  refine ⟨Q,?_,?_,tr⟩
  · unfold startingCursor
    dsimp only
    split
    · rename_i st hm
      have e := Pulse.again.inj (hm.symm.trans a)
      subst st
      rfl
    · rename_i hm
      rw [a] at hm
      cases hm
    · rename_i _ _ hm
      rw [a] at hm
      cases hm
  · unfold startingCursor
    dsimp only
    split <;> rfl

#print axioms positive_tape_weights
#print axioms genuine_cursor_start
#print axioms genuine_cursor_state
#print axioms startingCursor
#print axioms starting_cursor_exact
end J6R49DFS
