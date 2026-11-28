import V8R45PooledLiteralBundleConclusion
import V8R45PooledLiteralTranscript
import V8R45PooledLiteralFibers

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2700000
set_option maxRecDepth 2400

namespace V8R45PooledLiteral.PooledInput
open scoped Classical Polynomial
open Polynomial V8PooledRange
noncomputable section

variable {k : ℕ} {E : Type} [Fintype E] {H : Graph (Deficit k) E} {p : ThreePorts H} {f : ℤ[X]}
variable (I : PooledInput H p f)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem actual_adaptive_binary_answers_C6 (b : ℕ) (Q : I.Menu → Type*)
    (algorithm : ∀ m, BinaryTranscript (Q m) ℕ b)
    (answer : ∀ s, Q (I.computed s) → Bool)
    (correct : ∀ s, (algorithm (I.computed s)).run (answer s) = I.target s) :
    ((Fintype.card (Split.V k) : ℚ)-10)/12 ≤ ((I.bits+b : ℕ) : ℚ) := by
  let Side : I.Menu → Type := fun _ => Fin b → Bool
  let word (s : Split.V k → Bool) : Side (I.computed s) := (algorithm (I.computed s)).record (answer s)
  let dec (x : Sigma Side) : ℕ := (algorithm x.1).replay x.2
  exact I.exact_dependent_decoder_from_exterior_runs b Side
    (fun _ => (BinaryTranscript.word_count b).le) word dec
    (fun s => (BinaryTranscript.replay_record (answer s) (algorithm (I.computed s))).trans (correct s))

theorem actual_attainable_side_fiber_budget (b : ℕ)
    (S : I.Menu → Type*) (aux : ∀ s, S (I.computed s))
    (hS : ∀ m, Nat.card (UsedSide I.computed aux m) ≤ 2^b)
    (D : Sigma S → ℕ)
    (correct : ∀ s, D ⟨I.computed s,aux s⟩ = I.target s) :
    ((Fintype.card (Split.V k) : ℚ)-10)/12 ≤ ((I.bits+b : ℕ) : ℚ) := by
  let T := UsedSide I.computed aux
  letI (m : I.Menu) : Fintype (T m) := usedSideFintype I.computed aux m
  let dec (x : Sigma T) := D ⟨x.1,x.2.val⟩
  exact I.exact_dependent_decoder_from_exterior_runs b T
    (fun m => by rw [←Nat.card_eq_fintype_card]; exact hS m)
    (usedState I.computed aux) dec (fun s => (congrArg (fun a => D ⟨I.computed s,a⟩)
      (used_state_exact I.computed aux s)).trans (correct s))

#print axioms actual_adaptive_binary_answers_C6
#print axioms actual_attainable_side_fiber_budget
end
end V8R45PooledLiteral.PooledInput