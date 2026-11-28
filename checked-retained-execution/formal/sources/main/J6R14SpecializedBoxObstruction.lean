import J6R14SpecializedBoxRing
import J6R12RepackReadNatural

/-! A marked physical J9 row is genuinely weighted. Even at zero
higher tails, its actual factor at the all-false local assignment is
-1, whereas each unmodified J6 planted root table is 0 or 1. The
distinction below holds in the actual finite receiving ring, not just
over characteristic zero. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial NativeProbeRing DyadicProbeCompiler J6R9Recursive
open J8Physical J8EndToEnd J8J9Grouped J6R12Repack

theorem neg_one_ne_literal_bit (q : ℕ) (f : ℤ[X]) (ell : ℕ) (hf : f.Monic)
    (hq : 2 ≤ q) (hF : 0 < f.natDegree) (hℓ : 0 < ell) (b : Bool) :
    (-1:Box f ell q) ≠ (if b then 1 else 0) := by
  have hqw : 0 < q := by omega
  have hpow : 2 < (2:ℕ)^q :=
    (show 2 < (2:ℕ)^2 by decide).trans_le (Nat.pow_le_pow_right (by decide) hq)
  have rn (n : ℕ) (hn : n ≤ 2) := boxNatural_of_nat f ell q hf hqw hℓ hF n (hn.trans_lt hpow)
  cases b with
  | false =>
      change (-1:Box f ell q) ≠ 0
      intro he
      have h : (1:Box f ell q) = 0 := neg_eq_zero.mp he
      have hc := congrArg (boxNatural f ell q hf) h
      rw [show (1:Box f ell q)=((1:ℕ):Box f ell q) by simp,
          show (0:Box f ell q)=((0:ℕ):Box f ell q) by simp,
          rn 1 (by decide),rn 0 (by decide)] at hc
      omega
  | true =>
      change (-1:Box f ell q) ≠ 1
      intro he
      have h : (0:Box f ell q) = 2 := by
        calc
          _ = -1+1 := by ring
          _ = 1+1 := congrArg (·+1) he
          _ = _ := by ring
      have hc := congrArg (boxNatural f ell q hf) h
      rw [show (0:Box f ell q)=((0:ℕ):Box f ell q) by simp,
          show (2:Box f ell q)=((2:ℕ):Box f ell q) by simp,
          rn 0 (by decide),rn 2 (by decide)] at hc
      omega

variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

def falseAssignment (g : G) : (LocalPin d g→Bool) × LocalBits d g :=
  (fun _ => false, fun _ _ => false)

set_option linter.unusedSectionVars false in
theorem base_zero_on_false (e : EndpointSeating d) (even : Even L) (g : G)
    (r : LocalRow d g) (leg : Bool) :
    physicalBase d e even (J9FactorBounds.kernel L) (fun _ _ _ _ => 0)
      g (falseAssignment d g) r leg = 0 := by
  unfold physicalBase
  cases hh : localHit d e even r with
  | none => simp
  | some x => simp [falseAssignment,sourceBit]

set_option linter.unusedSectionVars false in
theorem marked_false_row_eval (e : EndpointSeating d) (even : Even L) (a : S)
    (j : TargetPorts d a) (q : ℕ) (f : ℤ[X]) (ell : ℕ) (z : Scalar q f) :
    let g := d.rowLabel (pinWire d a).1
    let x := falseAssignment d g
    let u := physicalBase d e even (J9FactorBounds.kernel L) (fun _ _ _ _ => 0)
    evalBox q f ell z (J8SourceMoment.rowFactor (J8SourceMoment.marker (some j) j.1)
      (u g x j.1 false) (u g x j.1 true)) = -1 := by
  dsimp only
  rw [base_zero_on_false d e even _ _ false,base_zero_on_false d e even _ _ true]
  simp [J8SourceMoment.marker,J8SourceMoment.rowFactor,J8SourceMoment.selectedEquality_eq]

set_option linter.unusedSectionVars false in
theorem marked_row_cannot_be_literal_bit (e : EndpointSeating d) (even : Even L) (a : S)
    (j : TargetPorts d a) (q : ℕ) (f : ℤ[X]) (ell : ℕ) (z : Scalar q f)
    (hf : f.Monic) (hq : 2 ≤ q) (hF : 0 < f.natDegree) (hℓ : 0 < ell) (b : Bool) :
    let g := d.rowLabel (pinWire d a).1
    let x := falseAssignment d g
    let u := physicalBase d e even (J9FactorBounds.kernel L) (fun _ _ _ _ => 0)
    evalBox q f ell z (J8SourceMoment.rowFactor (J8SourceMoment.marker (some j) j.1)
      (u g x j.1 false) (u g x j.1 true)) ≠ if b then 1 else 0 := by
  dsimp only
  rw [marked_false_row_eval d e even a j q f ell z]
  exact neg_one_ne_literal_bit q f ell hf hq hF hℓ b

#print axioms neg_one_ne_literal_bit
#print axioms base_zero_on_false
#print axioms marked_false_row_eval
#print axioms marked_row_cannot_be_literal_bit
end J6R14SpecializedBox
