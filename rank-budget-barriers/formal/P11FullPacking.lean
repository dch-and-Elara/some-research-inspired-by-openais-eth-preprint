import GuardedPacking
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic

/-!
The packetization of lines 149–167: ordered cells are literal words of ordered
symbol pairs; their type is the coordinatewise sorted pair. Each packet has
physical binary positions. Its convention can depend on the packet, but is
constant within that packet. The equal coordinates are precisely the copy bits.
-/
namespace P11FullPacking

open scoped BigOperators

abbrev Cell (I K : Type*) := I → K×K
abbrev Key (I K : Type*) [LE K] := {k : Cell I K // ∀ i, (k i).1 ≤ (k i).2}

variable {I K : Type*} [LinearOrder K]

def sortPair (p : K×K) : K×K := if p.1 ≤ p.2 then p else (p.2,p.1)

def key (c : Cell I K) : Key I K :=
  ⟨fun i => sortPair (c i), fun i => by
    by_cases h : (c i).1 ≤ (c i).2
    · simpa only [sortPair, if_pos h] using h
    · simpa only [sortPair, if_neg h] using (le_of_lt (lt_of_not_ge h))⟩

abbrev Hot (k : Key I K) := {i : I // (k.val i).1 ≠ (k.val i).2}
abbrev Cold (k : Key I K) := {i : I // (k.val i).1 = (k.val i).2}
abbrev Orient (k : Key I K) := Hot k → Bool
abbrev Copies (k : Key I K) := Cold k → Bool

def orientation (c : Cell I K) : Orient (key c) :=
  fun i => decide ((c i.val).2 < (c i.val).1)

def cell (k : Key I K) (m : Orient k) : Cell I K := fun i =>
  if h : (k.val i).1 ≠ (k.val i).2 then
    if m ⟨i,h⟩ then ((k.val i).2,(k.val i).1) else k.val i
  else k.val i

theorem cell_decode (c : Cell I K) : cell (key c) (orientation c) = c := by
  funext i
  change (if h : (sortPair (c i)).1 ≠ (sortPair (c i)).2 then
    if decide ((c i).2 < (c i).1) then ((sortPair (c i)).2,(sortPair (c i)).1) else sortPair (c i)
    else sortPair (c i)) = c i
  by_cases h : (c i).1 ≤ (c i).2
  · simp [sortPair, h, not_lt_of_ge h]
  · have ht := lt_of_not_ge h
    simp [sortPair, h, ht, ne_of_lt ht]

theorem key_cell (k : Key I K) (m : Orient k) : key (cell k m) = k := by
  apply Subtype.ext
  funext i
  change sortPair (cell k m i) = k.val i
  by_cases h : (k.val i).1 ≠ (k.val i).2
  · have hlt := lt_of_le_of_ne (k.prop i) h
    cases hm : m ⟨i,h⟩ <;> simp [cell, h, hm, sortPair, k.prop i, not_le_of_gt hlt]
  · simp [cell, h, sortPair, k.prop i]

theorem cell_injective (k : Key I K) : Function.Injective (cell k) := by
  intro m n he
  funext i
  have hc := congrFun he i.val
  have h := i.prop
  cases hm : m i <;> cases hn : n i <;>
    simp [cell, h, hm, hn] at hc ⊢
  · exact h (congrArg Prod.fst hc)
  · exact h (congrArg Prod.fst hc).symm

/-- Precisely one unordered type and orientation accompany every ordered
source label word. -/
noncomputable def cellChart : (Σ k : Key I K, Orient k) ≃ Cell I K := by
  refine Equiv.ofBijective (fun p => cell p.1 p.2) ⟨?_,?_⟩
  · rintro ⟨k,m⟩ ⟨l,n⟩ h
    change cell k m = cell l n at h
    have hkl : k=l := by
      have hh := congrArg key h
      rwa [key_cell, key_cell] at hh
    subst l
    have hm := cell_injective k h
    subst n
    rfl
  · intro c
    exact ⟨⟨key c,orientation c⟩,cell_decode c⟩

section PhysicalBits

def bits (a : ℕ) (x : Fin (2^a)) : Fin a → Bool := fun i => x.val.testBit i.val

theorem bits_injective (a : ℕ) : Function.Injective (bits a) := by
  intro x y h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<a
  · exact congrFun h ⟨i,hi⟩
  · have hx : x.val < 2^i := x.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have hy : y.val < 2^i := y.isLt.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    simp [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]

noncomputable def bitsChart (a : ℕ) : Fin (2^a) ≃ (Fin a → Bool) := by
  refine Equiv.ofBijective (bits a) ((Fintype.bijective_iff_injective_and_card _).2 ⟨bits_injective a,?_⟩)
  simp

theorem bitsChart_apply (a : ℕ) (x : Fin (2^a)) :
    bitsChart a x = bits a x := rfl

end PhysicalBits

variable {a : ℕ}

def shiftMask {J : Type*} (m d : J → Bool) : J → Bool :=
  fun i => if d i then !(m i) else m i

theorem shiftMask_cancel {J : Type*} (m c : J → Bool) :
    shiftMask m (fun i => decide (m i ≠ c i)) = c := by
  funext i
  cases hm : m i <;> cases hc : c i <;> simp [shiftMask,hm,hc]

theorem shiftMask_bits {J : Type*} (m d : J → Bool) :
    (fun i => decide (m i ≠ shiftMask m d i)) = d := by
  funext i
  cases hm : m i <;> cases hd : d i <;> simp [shiftMask,hm,hd]

def slotOrient (k : Key (Fin a) K) (m : Orient k) (x : Fin (2^a)) : Orient k :=
  shiftMask m (fun i => bits a x i.val)

abbrev LocalFiber (k : Key (Fin a) K) (m c : Orient k) :=
  {x : Fin (2^a) // slotOrient k m x = c}

/-- For a fixed orientation the equal-symbol coordinates remain completely
free; every physical position is represented by its original binary index. -/
noncomputable def copyChart (k : Key (Fin a) K) (m c : Orient k) :
    LocalFiber k m c ≃ Copies k := by
  classical
  let mkWord (f : Copies k) : Fin a → Bool := fun i =>
    if hn : (k.val i).1 ≠ (k.val i).2 then decide (m ⟨i,hn⟩ ≠ c ⟨i,hn⟩)
    else f ⟨i,not_ne_iff.mp hn⟩
  have hm (f : Copies k) : slotOrient k m ((bitsChart a).symm (mkWord f)) = c := by
    have hbits : bits a ((bitsChart a).symm (mkWord f)) = mkWord f :=
      (bitsChart a).apply_symm_apply _
    unfold slotOrient
    rw [hbits]
    have hx : (fun i : Hot k => mkWord f i.val) = (fun i => decide (m i ≠ c i)) := by
      funext i
      have hi := i.prop
      simp [mkWord, hi]
    rw [hx,shiftMask_cancel]
  refine
    { toFun := fun x i => bits a x.val i.val
      invFun := fun f => ⟨(bitsChart a).symm (mkWord f),hm f⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    apply Subtype.ext
    apply (bitsChart a).injective
    have he := (bitsChart a).apply_symm_apply (mkWord fun i => bits a x.val i.val)
    rw [he]
    change mkWord (fun i => bits a x.val i.val) = bits a x.val
    funext i
    by_cases hi : (k.val i).1 ≠ (k.val i).2
    · simp only [mkWord, dif_pos hi]
      have hb := shiftMask_bits m (fun j => bits a x.val j.val)
      change (fun j => decide (m j ≠ slotOrient k m x.val j)) = _ at hb
      rw [x.prop] at hb
      exact congrFun hb ⟨i,hi⟩
    · simp [mkWord, hi]
  · intro f
    funext i
    change bitsChart a ((bitsChart a).symm (mkWord f)) i.val = f i
    rw [(bitsChart a).apply_symm_apply]
    have hi := i.prop
    simp [mkWord, hi]

theorem hot_cold_card (k : Key (Fin a) K) :
    Nat.card (Hot k) + Nat.card (Cold k) = a := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (fun i : Fin a => (k.val i).1 = (k.val i).2),
    Fintype.card_fin, Nat.sub_add_cancel]
  exact Fintype.card_subtype_le _ |>.trans_eq (Fintype.card_fin _)

theorem copies_card (k : Key (Fin a) K) : Nat.card (Copies k) = 2^(a-Nat.card (Hot k)) := by
  classical
  rw [Nat.card_fun]
  simp only [Nat.card_eq_fintype_card (α:=Bool), Fintype.card_bool]
  have h := hot_cold_card k
  congr 1
  omega

theorem local_fiber_card (k : Key (Fin a) K) (m c : Orient k) :
    Nat.card (LocalFiber k m c) = 2^(a-Nat.card (Hot k)) := by
  rw [Nat.card_congr (copyChart k m c), copies_card]

theorem slotOrient_endpoint (k : Key (Fin a) K) (m : Orient k) (right : Bool)
    (x : Fin (2^a)) (hx : x.val = GuardedPacking.endpoint (2^a) right) :
    slotOrient k m x = GuardedPacking.endMask right m := by
  funext i
  have hi := i.val.isLt
  change (if x.val.testBit i.val.val then !m i else m i) = _
  rw [hx,GuardedPacking.endpoint_testBit a _ hi]
  rfl

#print axioms cell_decode
#print axioms key_cell
#print axioms cell_injective
#print axioms cellChart
#print axioms bitsChart
#print axioms copyChart
#print axioms bits_injective
#print axioms shiftMask_cancel
#print axioms shiftMask_bits
#print axioms hot_cold_card
#print axioms copies_card
#print axioms local_fiber_card
#print axioms slotOrient_endpoint

end P11FullPacking