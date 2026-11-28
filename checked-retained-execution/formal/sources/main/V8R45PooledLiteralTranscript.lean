import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
set_option maxRecDepth 2600

/-! The C6 paragraph explicitly allows up to b adaptive binary answers,
provided every address and stopping decision uses only previous public
observations. The exact tape below pads an early stop deterministically. -/
namespace V8R45PooledLiteral

inductive BinaryTranscript (Q R : Type*) : ℕ → Type _
  | finish {b : ℕ} : R → BinaryTranscript Q R b
  | request {b : ℕ} : Q → (Bool → BinaryTranscript Q R b) → BinaryTranscript Q R (b+1)

namespace BinaryTranscript
variable {Q R : Type*}

def run (answer : Q → Bool) : {b : ℕ} → BinaryTranscript Q R b → R
  | _, .finish r => r
  | _, .request q k => run answer (k (answer q))

def record (answer : Q → Bool) : {b : ℕ} → BinaryTranscript Q R b → Fin b → Bool
  | _, .finish _ => fun _ => false
  | _, .request q k => Fin.cases (answer q) (record answer (k (answer q)))

def replay : {b : ℕ} → BinaryTranscript Q R b → (Fin b → Bool) → R
  | _, .finish r, _ => r
  | _, .request _ k, w => replay (k (w 0)) (fun i => w i.succ)

theorem replay_record (answer : Q → Bool) :
    {b : ℕ} → (D : BinaryTranscript Q R b) → replay D (record answer D) = run answer D
  | _, .finish _ => rfl
  | _, .request q k => replay_record answer (k (answer q))

theorem word_count (b : ℕ) : Fintype.card (Fin b → Bool) = 2^b := by
  rw [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]

/-- A stop signal not selected by the previous answers constitutes an
additional input: at depth one these three possible states do not fit. -/
theorem externally_conveyed_stop_adds_states :
    2^1 < Fintype.card (Option Bool) := by decide

#print axioms replay_record
#print axioms word_count
#print axioms externally_conveyed_stop_adds_states
end BinaryTranscript


end V8R45PooledLiteral