import AOracleMachineTime

/-!
# Real tape addresses and threshold words

The tape head advances one cell at a time. At each visit, a Boolean
borrow circuit decrements the binary address; its underflow flag
selects the cell. The machine runs even on rejected out-of-range
indices. Shape and cost are proved against ordinary list indexing.
-/

namespace AOracleMachineTimeTape
open AOracleMachineTime

def borrowCore (borrow : Bool) : List Bool → Meter (List Bool × Bool)
  | [] => ⟨([],borrow),0⟩
  | a :: xs =>
    let y := borrowCore (!a && borrow) xs
    ⟨((a != borrow) :: y.result.1,y.result.2), y.steps+8⟩

theorem sub_bit (a b : Bool) :
    (a != b).toNat+b.toNat = a.toNat + 2*(!a && b).toNat := by
  cases a <;> cases b <;> decide

theorem borrow_exact (borrow : Bool) (xs : List Bool) :
    (borrowCore borrow xs).result.1.length=xs.length ∧
    bitsValue (borrowCore borrow xs).result.1 + borrow.toNat =
      bitsValue xs + 2^xs.length*(borrowCore borrow xs).result.2.toNat ∧
    (borrowCore borrow xs).steps=8*xs.length := by
  induction xs generalizing borrow with
  | nil => simp [borrowCore, bitsValue]
  | cons a xs ih =>
    obtain ⟨hl,hv,hs⟩ := ih (!a && borrow)
    have hbit := sub_bit a borrow
    simp only [borrowCore, List.length_cons, hl, hs, pow_succ, bitsValue]
    constructor
    · trivial
    · constructor
      · nlinarith
      · omega

theorem borrow_zero (xs : List Bool) :
    (borrowCore true xs).result.2=true ↔ bitsValue xs=0 := by
  obtain ⟨hl,hv,_hs⟩ := borrow_exact true xs
  have hlt := bitsValue_lt (borrowCore true xs).result.1
  rw [hl] at hlt
  cases h : (borrowCore true xs).result.2 <;> simp [h] at hv ⊢ <;> omega

theorem borrow_decreases (xs : List Bool) (hn : (borrowCore true xs).result.2=false) :
    bitsValue (borrowCore true xs).result.1+1=bitsValue xs := by
  simpa [hn] using (borrow_exact true xs).2.1

/-- The only conditional is the computed one-bit underflow flag. A
per-cell envelope covers bit I/O, address copy, and the constant
control steps; it does not regard an entire address as one bit. -/
def seek (a : List Bool) : List Bool → Meter (Option Bool)
  | [] => ⟨none,0⟩
  | b :: xs =>
    let s := borrowCore true a
    if s.result.2 then ⟨some b, s.steps+2*a.length+4⟩
    else
      let z := seek s.result.1 xs
      ⟨z.result,z.steps+s.steps+2*a.length+4⟩

theorem seek_exact (a data : List Bool) :
    (seek a data).result=data[bitsValue a]? ∧ (seek a data).steps≤(10*a.length+4)*data.length := by
  induction data generalizing a with
  | nil => simp [seek]
  | cons b xs ih =>
    obtain ⟨hl,_he,hs⟩ := borrow_exact true a
    unfold seek
    dsimp only
    cases hb : (borrowCore true a).result.2
    · rw [if_neg (by decide : false ≠ true)]
      obtain ⟨hr,hc⟩ := ih (borrowCore true a).result.1
      have hd := borrow_decreases a hb
      constructor
      · rw [hr, ← hd, List.getElem?_cons_succ]
      · rw [hl] at hc
        rw [hs, List.length_cons, Nat.mul_succ]
        dsimp only
        omega
    · rw [if_pos (rfl : true = true)]
      have hz := (borrow_zero a).mp hb
      constructor
      · rw [hz]
        rfl
      · rw [hs, List.length_cons, Nat.mul_succ]
        dsimp only
        omega

/-- Canonical input encoding. The arithmetic in this definition
describes the representation, not a machine oracle or data read. -/
def encodeBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | p+1, n => decide (n%2=1) :: encodeBits p (n/2)

theorem encodeBits_length (p n : ℕ) : (encodeBits p n).length=p := by
  induction p generalizing n with
  | zero => rfl
  | succ p ih => simp [encodeBits, ih]

theorem encodeBits_exact (p n : ℕ) (hn : n<2^p) : bitsValue (encodeBits p n)=n := by
  induction p generalizing n with
  | zero =>
    have : n=0 := by simpa using hn
    simp [encodeBits, bitsValue, this]
  | succ p ih =>
    rw [pow_succ] at hn
    have hd : n/2<2^p := by omega
    have hb : (decide (n%2=1)).toNat=n%2 := by
      by_cases h : n%2=1
      · simp [h]
      · simp [h]
        omega
    rw [encodeBits, bitsValue, hb, ih _ hd]
    omega

/-- Exact sought bit and its concrete scan envelope when the caller's
address fits a binary field. -/
theorem encoded_seek (p n : ℕ) (hn : n<2^p) (data : List Bool) :
    (seek (encodeBits p n) data).result=data[n]? ∧
      (seek (encodeBits p n) data).steps≤(10*p+4)*data.length := by
  simpa only [encodeBits_exact p n hn, encodeBits_length] using seek_exact (encodeBits p n) data

/-- The Boolean comparison is the original threshold acceptance
condition, with a literal ten-gate-per-bit envelope. -/
theorem threshold_machine (p d w : ℕ) (hd : d<2^p) (hw : w<2^p) :
    ((compareBits (encodeBits p d) (encodeBits p w)).result=true ↔ d<w) ∧
    (compareBits (encodeBits p d) (encodeBits p w)).steps=10*p := by
  have he := compareBits_exact (encodeBits p d) (encodeBits p w)
    (by rw [encodeBits_length, encodeBits_length])
  simpa only [encodeBits_exact p d hd, encodeBits_exact p w hw, encodeBits_length] using he

#print axioms borrow_exact
#print axioms seek_exact
#print axioms encodeBits_exact
#print axioms encoded_seek
#print axioms threshold_machine

end AOracleMachineTimeTape

