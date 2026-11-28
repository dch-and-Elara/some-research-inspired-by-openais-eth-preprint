
import A1R10Readout
import J6R14LayoutCostRanks

/-! Generate precisely the positive prefix 1,...,D+1, not the
entire residue field. Each emitted row is the exact least-significant-
bit-first probe word; carry and row writes have finite bit fees. -/
namespace J6R27PrescribedProbe
open A1R10 AOracleMachineTime AOracleMachineTimeTape J6R14LayoutCost
set_option maxHeartbeats 2500000

def encoded (e j : ℕ) : Word e :=
  ⟨encodeBits e j, encodeBits_length e j⟩

def emitPositive (e : ℕ) (one : Word e) : Word e → ℕ → Meter (List (Word e))
  | _,0 => ⟨[],4⟩
  | before,n+1 =>
    let increment := addWord before one
    let tail := emitPositive e one increment.result n
    ⟨increment.result::tail.result,increment.steps+tail.steps+8*e+6⟩

theorem encoded_succ (e j : ℕ) (he : 0<e) (fit : j+1<2^e) :
    let r := addWord (encoded e j) (wordOne e)
    r.result=encoded e (j+1) ∧ r.steps=12*e := by
  have h := succWord e j he fit
  exact ⟨Subtype.ext h.1,h.2⟩

theorem emit_positive_exact (e n j : ℕ) (he : 0<e) (fit : j+n<2^e) :
    let A := emitPositive e (wordOne e) (encoded e j) n
    A.result=List.ofFn (fun k : Fin n=>encoded e (j+k.val+1)) ∧
      A.steps=4+n*(20*e+6) := by
  induction n generalizing j with
  | zero => simp [emitPositive]
  | succ n ih =>
    have hp : j+1<2^e := by omega
    have hq : (j+1)+n<2^e := by omega
    obtain ⟨ie,ic⟩ := encoded_succ e j he hp
    obtain ⟨ee,ec⟩ := ih (j+1) hq
    dsimp only [emitPositive]
    rw [ie,ic,ee,ec]
    constructor
    · rw [List.ofFn_succ]
      simp only [Fin.val_zero,Nat.add_zero]
      congr 1
      apply congrArg List.ofFn
      funext i
      congr 1
      simp only [Fin.val_succ]
      omega
    · rw [Nat.succ_mul n (20*e+6)]
      omega

def positiveTape (e n : ℕ) : Meter (List (Word e)) :=
  let R := emitPositive e (wordOne e) (encoded e 0) n
  ⟨R.result,R.steps+3*e+6⟩

def positiveTapeFee (e n : ℕ) : ℕ :=
  4+n*(20*e+6)+3*e+6

theorem positive_tape_exact (e n : ℕ) (he : 0<e) (fit : n<2^e) :
    let R := positiveTape e n
    R.result=List.ofFn (fun i : Fin n=>encoded e (i.val+1)) ∧
    R.steps=positiveTapeFee e n := by
  obtain ⟨V,T⟩ := emit_positive_exact e n 0 he (by simpa only [Nat.zero_add] using fit)
  exact ⟨by simpa only [Nat.zero_add] using V, by
    change (emitPositive e (wordOne e) (encoded e 0) n).steps+3*e+6=_
    rw [T]
    rfl⟩

#print axioms encoded_succ
#print axioms emit_positive_exact
#print axioms positive_tape_exact
end J6R27PrescribedProbe
