
import J6R27OriginalGateModeCompare
import J6R27OriginalGateTrace

/-! Decode the actual recorded tile and positive Taylor weight. Compact
records are fixed bit words. The subtraction checks underflow and returns
a binary order word; it does not cast a supplied order oracle. -/
namespace J6R27OriginalGate
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R17ModeTape J6R21Ancestor

def readLow {q b : ℕ} (fit : b≤q) (a : Word q) : Meter (Word b) :=
  let z := copyBytes (a.bits.take b)
  ⟨⟨z.result,by
    change (copyBytes (a.bits.take b)).result.length=b
    rw [copyBytes_exact,List.length_take,a.size,Nat.min_eq_left fit]⟩,z.steps+2*b+4⟩

theorem read_low_fee {q b : ℕ} (fit : b≤q) (a : Word q) :
    (readLow fit a).steps=5*b+5 := by
  change (copyBytes (a.bits.take b)).steps+2*b+4=_
  rw [copyBytes_exact,List.length_take,a.size,Nat.min_eq_left fit]
  dsimp only
  omega

theorem take_encode_bits (b q x : ℕ) (fit : b≤q) :
    (encodeBits q x).take b=encodeBits b x := by
  induction b generalizing q x with
  | zero => rfl
  | succ b ih =>
    cases q with
    | zero => simp at fit
    | succ q =>
      change decide (x%2=1)::(encodeBits q (x/2)).take b = _
      rw [ih q (x/2) (Nat.le_of_succ_le_succ fit)]
      rfl

theorem read_low_word {q b : ℕ} (fit : b≤q) (n : ℕ) :
    (readLow fit (word (q:=q) n)).result=word n := by
  apply word_bits_inj
  change (copyBytes ((word (q:=q) n).bits.take b)).result=encodeBits b n
  rw [copyBytes_exact]
  exact take_encode_bits b q n fit

structure ModeNumbers (b q : ℕ) where
  tile : Word b
  order : Word q

def readModeNumbers {q b : ℕ} (fit : b≤q) (m : RawMode q) :
    Meter (Option (ModeNumbers b q)) :=
  let t := readLow fit m.tile
  let k := subtract m.weight (word 1)
  ⟨if k.result.2 then none else some ⟨t.result,k.result.1⟩,t.steps+k.steps+q+8⟩

theorem actual_mode_numbers {a pages p q : ℕ} (i : Fin a) (fit : i.val+1≤q)
    (hp : p<2^q) (m : PacketMode i pages (2^(i.val+1)) p) :
    let v := orderedMode i pages (2^(i.val+1)) p m
    let M := readModeNumbers fit (encodeMode (q:=q) i m)
    M.result=some ⟨word v.2.2.1.val,word v.2.2.2.val⟩ ∧
      M.steps=5*(i.val+1)+17*q+19 := by
  let v := orderedMode i pages (2^(i.val+1)) p m
  let w : Word q := word (v.2.2.2.val+1)
  let z := subtract w (word 1)
  have hq : 0<q := by have := i.isLt; omega
  have h1 : 1<(2:ℕ)^q := one_lt_pow₀ (by decide) hq.ne'
  have hW : v.2.2.2.val+1<p := by have := v.2.2.2.isLt; omega
  have hVal : w.val=v.2.2.2.val+1 := word_val (hW.trans hp)
  have E := subtract_exact w (word 1)
  change (z.result.2=false ↔ (word 1 : Word q).val≤w.val) ∧ _ at E
  have hR : z.result.2=false := E.1.mpr (by rw [word_val h1,hVal]; omega)
  have rVal := E.2.1 hR
  rw [hVal,word_val h1,Nat.add_sub_cancel] at rVal
  have R : z.result.1=word v.2.2.2.val :=
    (valued_word _).symm.trans (congrArg word rVal)
  change (if z.result.2 then none else some
      (⟨(readLow fit (word (q:=q) v.2.2.1.val)).result,z.result.1⟩ : ModeNumbers (i.val+1) q))=_ ∧
    (readLow fit (word (q:=q) v.2.2.1.val)).steps+z.steps+q+8=_
  rw [hR,read_low_word,read_low_fee,R,E.2.2]
  exact ⟨rfl,by omega⟩

#print axioms take_encode_bits
#print axioms read_low_word
#print axioms actual_mode_numbers
end J6R27OriginalGate



