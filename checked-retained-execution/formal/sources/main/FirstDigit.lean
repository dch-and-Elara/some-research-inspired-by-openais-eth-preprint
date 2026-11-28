import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Nat.Periodic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
Local first-extra-digit witness for completed Appendix D singleton slots.
The original row tables are literally three-literal Boolean clauses. The two
nonzero unary pin patterns are imposed before the row calculation. We model
the first reduced digit after normalization: only matching row residues have
unit normalized target coefficients, which act here as a common probe. The
global packet graph, crossing-coefficient valuation and packing certificate
are not introduced as new axioms or re-proved in this local module.
-/

namespace FirstDigit

open scoped BigOperators
open Finset

/-- s=true gives the positive third literal. -/
def literal (s w : Bool) : Bool := if s then w else !w

def clause (s u v w : Bool) : Bool := !u || !v || literal s w

def bit (R : Type*) [Zero R] [One R] (s : Bool) : R := if s then 1 else 0

def weight {R : Type*} [Ring R] (x : R) (s : Bool) : R := if s then x else 1-x

def literalAffine {R : Type*} [Ring R] (s : Bool) (w : R) : R := if s then w else 1-w

/-- Sum the original eight immutable truth-table entries. -/
def row {R : Type*} [CommRing R] (s : Bool) (u v w : R) : R :=
  ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
    bit R (clause s a b c) * weight u a * weight v b * weight w c

theorem row_formula {R : Type*} [CommRing R] (s : Bool) (u v w : R) :
    row s u v w = 1 - u*v*(1-literalAffine s w) := by
  cases s <;>
    simp [row, bit, weight, clause, literal, literalAffine] <;> ring

def firstLeg {R : Type*} [CommRing R] (s : Bool) (v w : R) : R :=
  row s 1 v w - row s 0 v w

/-- This is the exact coefficient of the changed U leg, over every ring. -/
theorem firstLeg_formula {R : Type*} [CommRing R] (s : Bool) (v w : R) :
    firstLeg s v w = -v*(1-literalAffine s w) := by
  simp [firstLeg, row_formula]

/-- Literal signed row sum at the U-address. Assigning U=0 gives coefficient
−1 and assigning U=1 gives +1, as in differentiation of its two affine lines. -/
theorem firstLeg_signed_table {R : Type*} [CommRing R] (s : Bool) (v w : R) :
    firstLeg s v w =
      ∑ a : Bool, ∑ b : Bool, ∑ c : Bool,
        bit R (clause s a b c) * (if a then 1 else -1) * weight v b * weight w c := by
  cases s <;>
    simp [firstLeg_formula, bit, weight, clause, literal, literalAffine] <;> ring

/-- Over the residue ring, the signs survive with their original bit values. -/
theorem firstLeg_modTwo (s : Bool) (v : ZMod 2) :
    firstLeg s v 0 = v * bit (ZMod 2) s := by
  cases s
  · simp [firstLeg_formula, literalAffine, bit]
  · have h : (-1 : ZMod 2) = 1 := by decide
    simp only [firstLeg_formula, literalAffine, if_true, sub_zero, mul_one, bit]
    calc
      -v = (-1 : ZMod 2) * v := (neg_one_mul v).symm
      _ = v := by rw [h, one_mul]

def lowPin (B L y : ℕ) : ZMod 2 := if y < B ∧ y < L then 1 else 0

def highPin (B L y : ℕ) : ZMod 2 := if L-B ≤ y ∧ y < L then 1 else 0

/-- Real matched-row interval for the V pin under a positive shift t. -/
def window (L B t : ℕ) : Finset ℕ := Finset.Ico (L-B-t) (L-t)

theorem low_shift_zero (B L t x : ℕ) (ht : B ≤ t) : lowPin B L (x+t) = 0 := by
  simp [lowPin, show ¬ x+t < B by omega]

theorem high_shift_eq (B L t x : ℕ) (ht : t+B ≤ L) :
    highPin B L (x+t) = if x ∈ window L B t then 1 else 0 := by
  have h : (L-B ≤ x+t ∧ x+t < L) ↔ x ∈ window L B t := by
    rw [window, Finset.mem_Ico]
    omega
  simp only [highPin, h]

def windowResidue (L B t τ : ℕ) : Finset ℕ :=
  (window L B t).filter (fun x => x % B = τ)

/-- A length-B interval contains exactly one row in every legal residue. -/
theorem card_windowResidue (L B t τ : ℕ) (ht : t+B ≤ L) (hr : τ<B) :
    (windowResidue L B t τ).card = 1 := by
  have hI : L-t = L-B-t+B := by omega
  have hp : Function.Periodic (fun x : ℕ => x % B = τ) B := by
    intro x
    change ((x+B)%B = τ) = (x%B = τ)
    rw [Nat.add_mod_right]
  unfold windowResidue window
  -- Rewriting both endpoints by hI would also change the lower one.
  have he : Finset.Ico (L-B-t) (L-t) = Finset.Ico (L-B-t) (L-B-t+B) :=
    congrArg (Finset.Ico (L-B-t)) hI
  rw [he, Nat.filter_Ico_card_eq_of_periodic _ _ _ hp, Nat.count_eq_card_filter_range]
  have he' : (Finset.range B).filter (fun x : ℕ => x % B = τ) = {τ} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hx,e⟩
      rwa [Nat.mod_eq_of_lt hx] at e
    · rintro rfl
      exact ⟨hr, Nat.mod_eq_of_lt hr⟩
  rw [he', Finset.card_singleton]

theorem window_unique (L B t τ : ℕ) (ht : t+B ≤ L) (hr : τ<B) :
    ∃ x, windowResidue L B t τ = {x} := Finset.card_eq_one.mp (card_windowResidue _ _ _ _ ht hr)

/-- Regroup the sum of all U column positions for b=0. Exactly the unique
predecessor-free pin in [0,B) with residue tau contributes. -/
def sourceMoment (B L τ : ℕ) : ZMod 2 :=
  ∑ y ∈ Finset.range L, if y%B = τ then lowPin B L y else 0

theorem sourceMoment_one (B L τ : ℕ) (hL : B≤L) (hr : τ<B) :
    sourceMoment B L τ = 1 := by
  have hs : (Finset.range L).filter (fun y => y%B = τ ∧ (y<B ∧ y<L)) = {τ} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hres, hlt, _⟩
      rwa [Nat.mod_eq_of_lt hlt] at hres
    · rintro rfl
      exact ⟨hr.trans_le hL, Nat.mod_eq_of_lt hr, hr, hr.trans_le hL⟩
  unfold sourceMoment lowPin
  have he (y : ℕ) :
      (if y % B = τ then (if y < B ∧ y < L then (1 : ZMod 2) else 0) else 0) =
      (if y % B = τ ∧ (y < B ∧ y < L) then 1 else 0) := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [← Finset.sum_filter, hs, Finset.sum_singleton]

/-- The literal completed singleton sum on the three packets: choose the
one targeted row; all other rows are contracted in their original order
through the row table. The coefficient support test is residue equality in
the first digit. -/
def singletonDigit (L B t τ : ℕ) (s : ℕ → Bool) : ZMod 2 :=
  sourceMoment B L τ *
    (∑ x ∈ Finset.range L,
      if x % B = τ then
        firstLeg (s x) (highPin B L (x+t)) 0 *
          ∏ y ∈ (Finset.range L).erase x,
            row (s y) (lowPin B L (y+t)) (highPin B L (y+t)) 0
      else 0)

/-- For a legal interior time, the normalized *whole local product* returns
the sign bit at the unique addressed original row. -/
theorem singletonDigit_exact (L B t τ : ℕ) (s : ℕ → Bool)
    (hlo : B ≤ t) (hhi : t+B≤L) (hr : τ<B) {x : ℕ}
    (hx : windowResidue L B t τ = {x}) :
    singletonDigit L B t τ s = bit (ZMod 2) (s x) := by
  unfold singletonDigit
  rw [sourceMoment_one _ _ _ (by omega) hr, one_mul]
  simp only [low_shift_zero _ _ _ _ hlo, row_formula, zero_mul, sub_zero, Finset.prod_const_one, mul_one,
    firstLeg_modTwo, high_shift_eq _ _ _ _ hhi, ite_mul, one_mul]
  have he (y : ℕ) :
      (if y % B = τ then (if y ∈ window L B t then bit (ZMod 2) (s y) else 0) else 0) =
      (if y % B = τ ∧ y ∈ window L B t then bit (ZMod 2) (s y) else 0) := by
    split_ifs <;> simp_all
  simp_rw [he]
  rw [← Finset.sum_filter]
  have hf : (Finset.range L).filter (fun y => y % B = τ ∧ y ∈ window L B t) =
      windowResidue L B t τ := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_range, windowResidue]
    have hib : y ∈ window L B t → y < L := by
      simp only [window, Finset.mem_Ico]; omega
    tauto
  rw [hf, hx, Finset.sum_singleton]

/-- Extending a nonzero probe still gives an injective encoding of one bit. -/
theorem probe_reads_bit_injectively {F : Type*} [Semiring F]
    (ψ : ZMod 2 →+* F) (z : F) (hz : z ≠ 0) :
    Function.Injective (fun s : Bool => z * ψ (bit (ZMod 2) s)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [bit]

/-- The original unshifted U,V pins have disjoint support; the undeformed
truth-table contraction of a triple is one regardless of its sign word. -/
theorem undeformed_one (L B : ℕ) (s : ℕ → Bool) (h : B+B≤L) :
    (∏ x ∈ Finset.range L, row (s x) (lowPin B L x) (highPin B L x) 0) = 1 := by
  apply Finset.prod_eq_one
  intro x _
  rw [row_formula]
  by_cases hx : x < B
  · have hv : ¬ (L-B ≤ x ∧ x < L) := by omega
    rw [highPin, if_neg hv]
    simp
  · simp [lowPin, hx]

/-- The same undeformed contraction equals one over the integers or any
other coefficient ring, not merely modulo two. -/
theorem undeformed_one_ring {R : Type*} [CommRing R] (L B : ℕ) (s : ℕ → Bool) (h : B+B≤L) :
    (∏ x ∈ Finset.range L,
      row (s x) (if x<B ∧ x<L then (1:R) else 0) (if L-B≤x ∧ x<L then (1:R) else 0) 0) = 1 := by
  apply Finset.prod_eq_one
  intro x _
  rw [row_formula]
  by_cases hx : x < B
  · have hv : ¬ (L-B ≤ x ∧ x<L) := by omega
    rw [if_neg hv]
    simp
  · have hu : ¬ (x < B ∧ x<L) := fun h' => hx h'.1
    rw [if_neg hu]
    simp

/-- The printed equally-spaced times are jB+3B/2. For a power-of-two B≥2
this is the same as jB+B+B/2; the Lean form permits any B. -/
def eligibleTime (B j : ℕ) : ℕ := B + B/2 + j*B

theorem time_interior (q B : ℕ) (j : Fin (q-2)) :
    B ≤ eligibleTime B j ∧ eligibleTime B j+B ≤ q*B := by
  have hj : j.val + 3 ≤ q := by have := j.isLt; omega
  have hm := Nat.mul_le_mul_right B hj
  rw [Nat.add_mul] at hm
  have hh := Nat.div_le_self B 2
  unfold eligibleTime
  omega

theorem times_separated (B : ℕ) {j j' : ℕ} (h : j < j') :
    eligibleTime B j + B ≤ eligibleTime B j' := by
  have hm := Nat.mul_le_mul_right B (Nat.succ_le_of_lt h)
  rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] at hm
  unfold eligibleTime
  omega

theorem windows_disjoint (L B t t' x : ℕ) (h : t+B≤t') (hi : t'+B≤L) :
    x ∈ window L B t → x ∉ window L B t' := by
  simp only [window, Finset.mem_Ico]
  omega

abbrev Address (q B : ℕ) := Fin (q-2) × Fin B

private theorem exists_row (q B : ℕ) (d : Address q B) :
    ∃ x : Fin (q*B), windowResidue (q*B) B (eligibleTime B d.1) d.2 = {x.val} := by
  obtain ⟨x,hx⟩ := window_unique (q*B) B (eligibleTime B d.1) d.2
    (time_interior q B d.1).2 d.2.isLt
  have hm : x ∈ windowResidue (q*B) B (eligibleTime B d.1) d.2 := by
    simp [hx]
  have hrow : x < q*B := by
    simp only [windowResidue, window, Finset.mem_filter, Finset.mem_Ico] at hm
    omega
  exact ⟨⟨x,hrow⟩, hx⟩

noncomputable def rowAddress (q B : ℕ) (d : Address q B) : Fin (q*B) :=
  Classical.choose (exists_row q B d)

theorem rowAddress_spec (q B : ℕ) (d : Address q B) :
    windowResidue (q*B) B (eligibleTime B d.1) d.2 = {(rowAddress q B d).val} :=
  Classical.choose_spec (exists_row q B d)

theorem rowAddress_injective (q B : ℕ) : Function.Injective (rowAddress q B) := by
  intro d e he
  have memd : (rowAddress q B d).val ∈ windowResidue (q*B) B (eligibleTime B d.1) d.2 := by
    simp [rowAddress_spec]
  have meme : (rowAddress q B d).val ∈ windowResidue (q*B) B (eligibleTime B e.1) e.2 := by
    rw [he, rowAddress_spec]
    exact Finset.mem_singleton_self _
  simp only [windowResidue, Finset.mem_filter] at memd meme
  have htimes : d.1 = e.1 := by
    apply Fin.ext
    by_contra! hneq
    rcases lt_or_gt_of_ne hneq with hlt | hgt
    · exact windows_disjoint _ _ _ _ _ (times_separated B hlt) (time_interior q B e.1).2 memd.1 meme.1
    · exact windows_disjoint _ _ _ _ _ (times_separated B hgt) (time_interior q B d.1).2 meme.1 memd.1
  exact Prod.ext htimes (Fin.ext (memd.2.symm.trans meme.2))

theorem addressed_digit (q B : ℕ) (d : Address q B) (s : ℕ → Bool) :
    singletonDigit (q*B) B (eligibleTime B d.1) d.2 s =
      bit (ZMod 2) (s (rowAddress q B d).val) :=
  singletonDigit_exact _ _ _ _ s (time_interior q B d.1).1 (time_interior q B d.1).2
    d.2.isLt (rowAddress_spec q B d)

noncomputable def signWord (q B : ℕ) (w : Address q B → Bool) (x : ℕ) : Bool :=
  if h : ∃ d : Address q B, (rowAddress q B d).val = x then w (Classical.choose h) else false

theorem signWord_at_address (q B : ℕ) (w : Address q B → Bool) (d : Address q B) :
    signWord q B w (rowAddress q B d).val = w d := by
  classical
  unfold signWord
  split_ifs with h
  · congr 1
    exact rowAddress_injective q B (Fin.ext (Classical.choose_spec h))
  · exact False.elim (h ⟨d,rfl⟩)

/-- Read local completed singleton digits at one public nonzero extension
probe; each address reads one independently assignable literal sign. -/
noncomputable def menu {F : Type*} [Semiring F] (ψ : ZMod 2 →+* F) (z : F)
    (q B : ℕ) (w : Address q B → Bool) (d : Address q B) : F :=
  z * ψ (singletonDigit (q*B) B (eligibleTime B d.1) d.2 (signWord q B w))

theorem menu_reads_exact {F : Type*} [Semiring F] (ψ : ZMod 2 →+* F) (z : F)
    (q B : ℕ) (w : Address q B → Bool) (d : Address q B) :
    menu ψ z q B w d = z * ψ (bit (ZMod 2) (w d)) := by
  rw [menu, addressed_digit, signWord_at_address]

theorem menu_injective {F : Type*} [Semiring F] (ψ : ZMod 2 →+* F) (z : F) (hz : z≠0)
    (q B : ℕ) : Function.Injective (menu ψ z q B) := by
  intro w w' e
  funext d
  have hd := congrFun e d
  rw [menu_reads_exact, menu_reads_exact] at hd
  exact probe_reads_bit_injectively ψ z hz hd

/-- Exactly 2^(L-2B) distinct menus are attained on the chosen independently
assignable sign words in one triple, for L=qB. This does not count layout
types or infer the cost of acquiring one menu entry. -/
theorem menu_card {F : Type*} [Semiring F] (ψ : ZMod 2 →+* F) (z : F) (hz : z≠0)
    (q B : ℕ) : Nat.card (Set.range (menu ψ z q B)) = 2^(q*B - 2*B) := by
  classical
  rw [Nat.card_range_of_injective (menu_injective ψ z hz q B), Nat.card_fun]
  simp [Nat.sub_mul]

#print axioms row_formula
#print axioms firstLeg_formula
#print axioms firstLeg_signed_table
#print axioms firstLeg_modTwo
#print axioms low_shift_zero
#print axioms high_shift_eq
#print axioms card_windowResidue
#print axioms window_unique
#print axioms sourceMoment_one
#print axioms singletonDigit_exact
#print axioms probe_reads_bit_injectively
#print axioms undeformed_one
#print axioms undeformed_one_ring
#print axioms time_interior
#print axioms times_separated
#print axioms windows_disjoint
#print axioms rowAddress_spec
#print axioms rowAddress_injective
#print axioms addressed_digit
#print axioms signWord_at_address
#print axioms menu_reads_exact
#print axioms menu_injective
#print axioms menu_card

end FirstDigit