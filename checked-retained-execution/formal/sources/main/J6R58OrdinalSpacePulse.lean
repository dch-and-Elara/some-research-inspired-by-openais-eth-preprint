import J6R25PreparedSupplyDrain

/-! One actual weighted pulse carries its own rank counter. Its result
contains the one actual emitted row, one ordinal, the existing cursor
and the updated ordinal. The legacy catalogue and the mathematical
future-recursion witness are not runtime arguments. -/
namespace J6R58OrdinalSpace
open AOracleMachineTime J6R15ModeCost J6R25PreparedSupply
set_option autoImplicit false
set_option maxHeartbeats 8000000

inductive NumberedPulse (q n bits : ℕ) where
  | again
  | halt
  | emit : List (Word q)→Word bits→Pending q n→Word bits→NumberedPulse q n bits

def numberedPulse {q n bits : ℕ} (p : Pending q n) (i : Word bits) :
    Meter (NumberedPulse q n bits) :=
  let z := p.pulse
  match e : z.result with
  | .again _ => ⟨.again,z.steps⟩
  | .halt => ⟨.halt,z.steps⟩
  | .emit raw _ =>
    let nextOrdinal := increment i
    ⟨.emit raw i (p.tail e) nextOrdinal.result,
      z.steps+nextOrdinal.steps+3⟩

-- The literal bit tape is written directly (one false bit per lane).
def firstOrdinal (bits : ℕ) : Meter (Word bits) := ⟨zeroWord bits,3*bits+1⟩

theorem first_ordinal_is_paid_zero (bits : ℕ) :
    (firstOrdinal bits).result.val=0 ∧ (firstOrdinal bits).steps=3*bits+1 := by
  exact ⟨zeroWord_val bits,rfl⟩

theorem one_actual_emission_carries_exactly_its_existing_word {q n bits : ℕ}
    (p : Pending q n) (i : Word bits) {raw : List (Word q)} {state : State q}
    (e : p.pulse.result=.emit raw state) :
    numberedPulse p i=
      ⟨.emit raw i (p.tail e) (increment i).result,p.pulse.steps+(increment i).steps+3⟩ := by
  unfold numberedPulse
  dsimp only
  split
  · rename_i _ mismatch
    rw [e] at mismatch
    cases mismatch
  · rename_i mismatch
    rw [e] at mismatch
    cases mismatch
  · rename_i raw' state' eq
    have h := eq.symm.trans e
    cases h
    rfl

theorem actual_rank_step_is_fixed_word_and_charged {q n bits : ℕ}
    (p : Pending q n) (i : Word bits) {raw : List (Word q)} {state : State q}
    (e : p.pulse.result=.emit raw state) (pos : 0<bits) (room : i.val+1<2^bits) :
    let out := numberedPulse p i
    out.result=.emit raw i (p.tail e) (increment i).result ∧
    out.steps=p.pulse.steps+(13*bits+4)+3 ∧
    (increment i).result.val=i.val+1 ∧ (increment i).result.bits.length=bits := by
  have next := increment_exact pos i room
  dsimp only
  rw [one_actual_emission_carries_exactly_its_existing_word p i e]
  exact ⟨rfl,by rw [next.2],next.1,(increment i).result.size⟩

#print axioms first_ordinal_is_paid_zero
#print axioms one_actual_emission_carries_exactly_its_existing_word
#print axioms actual_rank_step_is_fixed_word_and_charged
end J6R58OrdinalSpace
