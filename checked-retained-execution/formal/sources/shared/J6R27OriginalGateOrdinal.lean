
import J6R25PreparedSupplyPorts

/-! Find an edge's sequential bit position from its physical address.
The executable scan uses fixed bit words, compares every visited address,
and advances a ripple counter on misses. The mathematical index occurs
only in the correctness theorem, not in the scan input. -/
namespace J6R27OriginalGate
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor

def scanOrdinal {a b : ℕ} (key : Word a) (pos : Word b) :
    List (Word a) → Meter (Option (Word b))
  | [] => ⟨none,2⟩
  | addr::rest =>
    let seen := cmpAddr key addr
    if seen.result then
      ⟨some pos,seen.steps+b+4⟩
    else
      let next := increment pos
      let later := scanOrdinal key next.result rest
      ⟨later.result,seen.steps+next.steps+later.steps+6⟩

def missFee (a b : ℕ) := 10*a+13*b+15
def hitFee (a b : ℕ) := 10*a+b+9

private theorem increment_fee {b : ℕ} (pos : Word b) :
    (increment pos).steps=13*b+4 := by
  have h := (addBits_exact pos.bits (encodeBits b 1) (by rw [pos.size,encodeBits_length])).2.2
  change (addBits pos.bits (encodeBits b 1)).steps+b+4=_
  rw [h,pos.size]
  omega

theorem scan_ordinal_absent {a b : ℕ} (key : Word a) (pos : Word b)
    (rows : List (Word a)) (hn : key ∉ rows) :
    scanOrdinal key pos rows=⟨none,rows.length*missFee a b+2⟩ := by
  induction rows generalizing pos with
  | nil => simp [scanOrdinal]
  | cons row rs ih =>
    rw [List.mem_cons,not_or] at hn
    rw [scanOrdinal,if_neg (fun h=>hn.1 ((cmpAddr_exact _ _).1.mp h))]
    dsimp only
    rw [ih _ hn.2]
    simp only [(cmpAddr_exact _ _).2,increment_fee,List.length_cons,Nat.add_mul,one_mul,missFee]
    congr 1
    omega

theorem scan_ordinal_hit {a b : ℕ} (hb : 0<b) (key : Word a) (pos : Word b)
    (before after : List (Word a)) (miss : key∉before)
    (fit : pos.val+before.length<2^b) :
    scanOrdinal key pos (before++key::after) =
      ⟨some (word (pos.val+before.length)),before.length*missFee a b+hitFee a b⟩ := by
  induction before generalizing pos with
  | nil =>
    simp only [List.nil_append,List.length_nil,Nat.add_zero,Nat.zero_mul,Nat.zero_add]
    rw [scanOrdinal,if_pos ((cmpAddr_exact _ _).1.mpr rfl),(cmpAddr_exact _ _).2,
      valued_word pos,hitFee]
    congr 1; omega
  | cons addr pre ih =>
    rw [List.mem_cons,not_or] at miss
    have h1 : pos.val+1<2^b := by simpa only [List.length_cons] using
      (show pos.val+1<2^b from (show pos.val+1≤pos.val+(addr::pre).length by
        simp only [List.length_cons]; omega).trans_lt fit)
    obtain ⟨hv,hc⟩ := increment_exact hb pos h1
    have hf : (increment pos).result.val+pre.length<2^b := by
      rw [hv]
      simpa only [List.length_cons] using
        (show pos.val+1+pre.length<2^b from (by rw [Nat.add_right_comm]; exact fit))
    rw [List.cons_append,scanOrdinal,if_neg (fun h=>miss.1 ((cmpAddr_exact _ _).1.mp h))]
    dsimp only
    rw [ih _ miss.2 hf,(cmpAddr_exact _ _).2,hv,hc]
    have hn : pos.val+1+pre.length=pos.val+(addr::pre).length := by
      simp only [List.length_cons]
      omega
    rw [hn]
    simp only [List.length_cons,Nat.add_mul,one_mul,missFee]
    congr 1
    omega

def findOrdinal {a : ℕ} (b : ℕ) (key : Word a) (rows : List (Word a)) :
    Meter (Option (Word b)) :=
  let out := scanOrdinal key (word 0) rows
  ⟨out.result,out.steps+b+3⟩

theorem find_ordinal_split {a b : ℕ} (hb : 0<b) (key : Word a)
    (before after : List (Word a)) (miss : key∉before) (fit : before.length<2^b) :
    findOrdinal b key (before++key::after)=
      ⟨some (word before.length),before.length*missFee a b+hitFee a b+b+3⟩ := by
  unfold findOrdinal
  have h0 : (word (q:=b) 0).val=0 := word_val (by positivity)
  rw [scan_ordinal_hit hb key _ before after miss (by rw [h0,Nat.zero_add]; exact fit),h0,Nat.zero_add]

/-- Every representative occupies its true sibling-tape position. The proof
uses equality of the actual address bytes and uniqueness, not a serialized
index/value dictionary. -/
theorem find_ordinal_indexed {a b n : ℕ} (hb : 0<b) (f : Fin n→Word a)
    (unique : Function.Injective f) (fit : n≤2^b) (j : Fin n) :
    findOrdinal b (f j) (List.ofFn f) =
      ⟨some (word j.val),j.val*missFee a b+hitFee a b+b+3⟩ := by
  let xs := List.ofFn f
  have jL : j.val<xs.length := by simp [xs]
  have atJ : xs[j.val]=f j := List.getElem_ofFn jL
  have split : xs=xs.take j.val++f j::xs.drop (j.val+1) := by
    calc
      xs = xs.take j.val++xs.drop j.val := (List.take_append_drop _ _).symm
      _ = _ := by rw [List.drop_eq_getElem_cons jL,atJ]
  have miss : f j∉xs.take j.val := by
    intro H
    obtain ⟨i,hi,he⟩ := List.mem_take_iff_getElem.mp H
    have him : i<n := by
      have hi' := hi.trans_le (Nat.min_le_right _ _)
      simpa [xs] using hi'
    have e : f (⟨i,him⟩ : Fin n)=f j := by
      simpa only [xs,List.getElem_ofFn] using he
    have eq := congrArg Fin.val (unique e)
    change i=j.val at eq
    have lower := hi.trans_le (Nat.min_le_left _ _)
    omega
  have tlen : (xs.take j.val).length=j.val := List.length_take_of_le jL.le
  have H := find_ordinal_split hb (f j) (xs.take j.val) (xs.drop (j.val+1)) miss
    (by rw [tlen]; exact j.isLt.trans_le fit)
  rw [tlen,←split] at H
  exact H

#print axioms find_ordinal_indexed
#print axioms scan_ordinal_absent
#print axioms scan_ordinal_hit
#print axioms find_ordinal_split
end J6R27OriginalGate




