import J6R17ModeTapeDispatch
import J6R25PreparedSupplyRegistry

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5500000

/-! Literal word-level mode dispatch. The current ordinal is a mutable
binary register, and the declared next register is incremented once per
emission, not once per group. Old ordinal conventions are joined later. -/
namespace J6R50ModeDispatch
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply

structure OpenMode (q tm : ℕ) where
  word : Word tm
  next : Word tm
  support : List (RawMode q × Word q)

def prepareMode {q tm : ℕ} (a : ℕ) (roster : List (RawMode q))
    (raw : List (Word q)) (ordinal : Word tm) : Meter (Option (OpenMode q tm)) :=
  let s := emitSupport a roster raw
  match s.result with
  | none => ⟨none,s.steps+3⟩
  | some sparse =>
    let next := increment ordinal
    ⟨some ⟨ordinal,next.result,sparse⟩,s.steps+next.steps+5⟩

theorem prepare_emitted_mode_exact {q tm : ℕ} (a : ℕ) (roster : List (RawMode q))
    (raw : List (Word q)) (ordinal : Word tm) (hn : roster.length=raw.length)
    (ht : 0<tm) (fit : ordinal.val+1<2^tm) :
    let out := prepareMode a roster raw ordinal
    let next := increment ordinal
    out.result=some ⟨ordinal,next.result,supportSpec roster raw⟩ ∧
    next.result.val=ordinal.val+1 ∧
    out.steps=roster.length*dispatchStride a q+13*tm+13 := by
  obtain ⟨v,c⟩ := emitSupport_exact a roster raw hn
  obtain ⟨n,k⟩ := increment_exact ht ordinal fit
  dsimp only
  refine ⟨?_,n,?_⟩
  · unfold prepareMode
    dsimp only
    rw [v]
  · unfold prepareMode
    dsimp only
    rw [v]
    dsimp only
    rw [c,k]
    omega

/-- One group of an already prepared emitted mode. This copies the
same physical bits consumed by the native four-field issuer. -/
def issueGroup {q tm tc tz : ℕ} (t : Word tc) (z : Word tz)
    (m : OpenMode q tm) (g : Word 6) : Meter (Word (tc+(tz+(tm+6)))) :=
  preparedKey t z m.word g

theorem issue_group_is_billed {q tm tc tz : ℕ} (t : Word tc) (z : Word tz)
    (m : OpenMode q tm) (g : Word 6) :
    (issueGroup t z m g).result=joinKey t (joinKey z (joinKey m.word g)) ∧
    (issueGroup t z m g).steps=6*(tc+(tz+(tm+6)))+10 :=
  prepared_key_exact t z m.word g

theorem group_address_recovers_fields {q tm tc tz : ℕ} (t t' : Word tc) (z z' : Word tz)
    (m m' : OpenMode q tm) (g g' : Word 6)
    (h : (issueGroup t z m g).result=(issueGroup t' z' m' g').result) :
    t=t' ∧ z=z' ∧ m.word=m'.word ∧ g=g' :=
  prepared_key_injective h

#print axioms prepareMode
#print axioms prepare_emitted_mode_exact
#print axioms issue_group_is_billed
#print axioms group_address_recovers_fields
end J6R50ModeDispatch

