import BareissHeightDense
import AffineCostMatrix
import BareissArithmetic

/-!
The actual bit arithmetic for constructing the augmented evaluation systems.
Unreduced input fractions can be used directly. The nonzero denominator of
each label is raised to the output degree and clears that node's equations.
-/

namespace Reconstruction.BareissPaper

open AffineEdge BareissHeight
open AffineCost.Bit (Run Signed Fraction)
open scoped BigOperators

private def zeroS := Signed.ofBool false
private def oneS := Signed.ofBool true

private theorem zeroS_number : zeroS.number = 0 := rfl
private theorem oneS_number : oneS.number = 1 := rfl
private theorem zeroS_size : zeroS.size = 0 := rfl
private theorem oneS_size : oneS.size = 1 := rfl

/-- Repeated bit-string multiplication, with an explicit charge for every iteration. -/
def signedPower (a : Signed) : ℕ → Run Signed
  | 0 => ⟨oneS, 8⟩
  | k+1 =>
    let p := signedPower a k
    let m := Signed.mul a p.value
    ⟨m.value, 16 + p.steps + m.steps⟩

@[simp] theorem signedPower_number (a : Signed) (k : ℕ) :
    (signedPower a k).value.number = a.number^k := by
  induction k with
  | zero => simp [signedPower, oneS_number]
  | succ k ih => simp [signedPower, ih, pow_succ, mul_comm]

theorem signedPower_size (a : Signed) (k L : ℕ) (ha : a.size ≤ L) :
    (signedPower a k).value.size ≤ 1+k*(L+1) := by
  induction k with
  | zero => simp [signedPower, oneS_size]
  | succ k ih =>
    have hm := Signed.mul_size a (signedPower a k).value
    simp only [signedPower, Nat.succ_mul]
    omega

def generationWidth (q L : ℕ) : ℕ := 4*(q+2)*(L+2)

private theorem generationWidth_ge (q L : ℕ) :
    2*(1+q*(L+1))+1 ≤ generationWidth q L := by
  unfold generationWidth
  nlinarith only [Nat.zero_le q, Nat.zero_le L, Nat.zero_le (q*L)]

def powerStage (q L : ℕ) : ℕ := 16+4096*(generationWidth q L)^2

theorem signedPower_steps (a : Signed) (k q L : ℕ) (ha : a.size ≤ L) (hk : k ≤ q) :
    (signedPower a k).steps ≤ 8+k*powerStage q L := by
  induction k with
  | zero => simp [signedPower]
  | succ k ih =>
    have hk' : k ≤ q := by omega
    have hpk := signedPower_size a k L ha
    have hmono := Nat.mul_le_mul_right (L+1) hk'
    have hu : a.size + (signedPower a k).value.size + 1 ≤ generationWidth q L := by
      have hh := generationWidth_ge q L
      have hqq : L ≤ q*(L+1) :=
        (Nat.le_succ L).trans (Nat.le_mul_of_pos_left _ (by omega))
      omega
    have hm := (Signed.mul_steps a (signedPower a k).value).trans
      (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left hu 2))
    have hsub := ih hk'
    simp only [signedPower, Nat.succ_mul]
    unfold powerStage at hsub ⊢
    omega

/-- Binary measurement coefficient. The physical scan distinguishes the two
nonzero column shapes in (5). -/
def encoderBit {q : ℕ} (j : EncoderRow q) (v : Word q) : Bool :=
  match AffineCost.scan v v, j with
  | .zero, .inr (.inr k) => k == parity v.1
  | .one s, .inl t => t == s
  | .one s, .inr (.inl k) => (k == bucket s) && v.1 s
  | _, _ => false

theorem encoderBit_spec {q : ℕ} (j : EncoderRow q) (v : Word q) :
    (if encoderBit j v then (1:ℚ) else 0) = encoderAt j v := by
  unfold encoderBit encoderAt
  cases AffineCost.scan v v <;> rcases j with (j | j | j) <;> simp [encoderColumn, bitScalar]
  split <;> simp_all

/-- Allowance for computing and comparing bounded metadata, including the
physical-word scan and the positional row and column indices. -/
def entryControl (D q : ℕ) : ℕ := 128*(D+q+2)^4

private def computedEntry {q : ℕ} (a : Fraction) (u : Word q)
    (e : Equation q) (j : Option (Unknown q)) : Run Signed :=
  let t := e.1
  let v := e.2
  if v.1 t == u.2 t then ⟨zeroS, 0⟩ else
    match j with
    | none =>
        if AffineCost.wordEqual u v then
          let p := signedPower a.den (q-2)
          ⟨p.value.neg, p.steps+8⟩
        else ⟨zeroS,0⟩
    | some (.inl (w,k)) =>
        if AffineCost.wordEqual w v then
          let p := signedPower a.num (k.val+1)
          let d := signedPower a.den (q-2-(k.val+1))
          let r := Signed.mul p.value d.value
          ⟨r.value, p.steps+d.steps+r.steps⟩
        else ⟨zeroS,0⟩
    | some (.inr (s,k)) =>
        if (s == t) && encoderBit k v then
          let p := signedPower a.den (q-2)
          ⟨p.value.neg, p.steps+8⟩
        else ⟨zeroS,0⟩

/-- Construct one addressed integer entry from raw encoded rational labels. -/
def buildEntry {q : ℕ} (a : Fin q → Fraction) (u : Word q)
    (e : Equation q) (j : Option (Unknown q)) : Run Signed :=
  let r := computedEntry (a e.1) u e j
  ⟨r.value, entryControl (wordCount q) q + r.steps⟩

/-- The matrix handed to elimination, interpreted in the integers. -/
def generatedInt {q : ℕ} (a : Fin q → Fraction) (u : Word q) :
    Matrix (Fin (equationCount q)) (Option (Fin (unknownCount q))) ℤ :=
  Matrix.of fun i j => (buildEntry a u ((equationIndex q).symm i) (j.map (unknownIndex q).symm)).value.number

/-- The arithmetic cost of one entry, including its control allowance. -/
def entryBudget (D q L : ℕ) : ℕ :=
  entryControl D q + 32 + (2*q+1)*powerStage q L

theorem buildEntry_size {q L : ℕ} (a : Fin q → Fraction) (u : Word q)
    (h : ∀ t, (a t).size ≤ L) (e : Equation q) (j : Option (Unknown q)) :
    (buildEntry a u e j).value.size ≤ generationWidth q L := by
  rcases e with ⟨t,v⟩
  have hnum := (Fraction.num_size (a t)).trans (h t)
  have hden := (Fraction.den_size (a t)).trans (h t)
  have hw := generationWidth_ge q L
  have hdenpow (d : ℕ) (hd : d ≤ q) :
      (signedPower (a t).den d).value.size ≤ 1+q*(L+1) :=
    (signedPower_size _ _ _ hden).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _)
  have hnumpow (d : ℕ) (hd : d ≤ q) :
      (signedPower (a t).num d).value.size ≤ 1+q*(L+1) :=
    (signedPower_size _ _ _ hnum).trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _)
  by_cases hv : (v.1 t == u.2 t) = true
  · simp [buildEntry, computedEntry, hv, zeroS_size]
  · cases j with
    | none =>
      by_cases he : AffineCost.wordEqual u v = true
      · simp only [buildEntry, computedEntry, hv, Bool.false_eq_true, if_false, he, if_true, Signed.neg_size]
        exact (hdenpow (q-2) (by omega)).trans (by omega)
      · simp [buildEntry, computedEntry, hv, he, zeroS_size]
    | some j =>
      rcases j with ⟨w,i⟩ | ⟨s,k⟩
      · by_cases he : AffineCost.wordEqual w v = true
        · have hi := i.isLt
          have hp := hnumpow (i.val+1) (by omega)
          have hd := hdenpow (q-2-(i.val+1)) (by omega)
          simp only [buildEntry, computedEntry, hv, Bool.false_eq_true, if_false, he, if_true]
          exact (Signed.mul_size _ _).trans (by omega)
        · simp [buildEntry, computedEntry, hv, he, zeroS_size]
      · by_cases he : (s == t && encoderBit k v) = true
        · simp only [buildEntry, computedEntry, hv, Bool.false_eq_true, if_false, he, if_true, Signed.neg_size]
          exact (hdenpow (q-2) (by omega)).trans (by omega)
        · simp [buildEntry, computedEntry, hv, he, zeroS_size]

theorem buildEntry_steps {q L : ℕ} (a : Fin q → Fraction) (u : Word q)
    (h : ∀ t, (a t).size ≤ L) (e : Equation q) (j : Option (Unknown q)) :
    (buildEntry a u e j).steps ≤ entryBudget (wordCount q) q L := by
  rcases e with ⟨t,v⟩
  have hnum := (Fraction.num_size (a t)).trans (h t)
  have hden := (Fraction.den_size (a t)).trans (h t)
  have hw := generationWidth_ge q L
  have hdenSteps (d : ℕ) (hd : d ≤ q) :
      (signedPower (a t).den d).steps ≤ 8+q*powerStage q L :=
    (signedPower_steps _ _ _ _ hden hd).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hd) _)
  rw [entryBudget, Nat.add_mul, Nat.mul_assoc]
  by_cases hv : (v.1 t == u.2 t) = true
  · simp only [buildEntry, computedEntry, hv, if_true]
    omega
  · cases j with
    | none =>
      by_cases he : AffineCost.wordEqual u v = true
      · have hs := hdenSteps (q-2) (by omega)
        simp only [buildEntry, computedEntry, hv, Bool.false_eq_true, if_false, he, if_true]
        omega
      · simp only [buildEntry, computedEntry, hv, Bool.false_eq_true, if_false, he]
        omega
    | some j =>
      rcases j with ⟨w,i⟩ | ⟨s,k⟩
      · by_cases he : AffineCost.wordEqual w v = true
        · have hi : i.val+1 ≤ q := by have := i.isLt; omega
          let p := signedPower (a t).num (i.val+1)
          let d := signedPower (a t).den (q-2-(i.val+1))
          have hp := (signedPower_steps _ _ q _ hnum hi).trans
            (Nat.add_le_add_left (Nat.mul_le_mul_right _ hi) _)
          have hd := hdenSteps (q-2-(i.val+1)) (by omega)
          have hp' := signedPower_size (a t).num (i.val+1) L hnum
          have hd' := signedPower_size (a t).den (q-2-(i.val+1)) L hden
          have hpq := Nat.mul_le_mul_right (L+1) hi
          have hdq := Nat.mul_le_mul_right (L+1) (show q-2-(i.val+1) ≤ q by omega)
          have hu : p.value.size+d.value.size+1 ≤ generationWidth q L := by
            dsimp [p,d]
            omega
          have hm := (Signed.mul_steps p.value d.value).trans
            (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left hu 2))
          simp only [buildEntry, computedEntry, hv, Bool.false_eq_true, if_false, he, if_true]
          dsimp [p,d] at hm
          unfold powerStage at *
          omega
        · simp only [buildEntry, computedEntry, hv, Bool.false_eq_true, if_false, he]
          omega
      · by_cases he : (s == t && encoderBit k v) = true
        · have hs := hdenSteps (q-2) (by omega)
          simp only [buildEntry, computedEntry, hv, Bool.false_eq_true, if_false, he, if_true]
          omega
        · simp only [buildEntry, computedEntry, hv, Bool.false_eq_true, if_false, he]
          omega

theorem signed_natAbs_lt {a : Signed} {B : ℕ} (ha : a.size ≤ B) :
    a.number.natAbs < 2^B := by
  have p := (AffineCost.Bit.value_lt a.plus).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
      ((le_max_left a.plus.length a.minus.length).trans ha))
  have n := (AffineCost.Bit.value_lt a.minus).trans_le
    (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
      ((le_max_right a.plus.length a.minus.length).trans ha))
  have p' : (AffineCost.Bit.value a.plus : ℤ) < (2:ℤ)^B := by exact_mod_cast p
  have n' : (AffineCost.Bit.value a.minus : ℤ) < (2:ℤ)^B := by exact_mod_cast n
  have hv : |a.number| < (2:ℤ)^B := by
    rw [abs_lt, Signed.number]
    omega
  rw [Int.abs_eq_natAbs] at hv
  exact_mod_cast hv

theorem generatedInt_height {q L : ℕ} (a : Fin q → Fraction) (u : Word q)
    (h : ∀ t, (a t).size ≤ L) (i j) :
    (generatedInt a u i j).natAbs ≤ 2^(generationWidth q L) :=
  (signed_natAbs_lt (buildEntry_size a u h _ _)).le

def physicalLabels {q : ℕ} (a : Fin q → Fraction) : Fin q → ℚ := fun t => (a t).rat

private theorem den_mul_rat (a : Fraction) (ha : a.valid) :
    (a.den.number : ℚ) * a.rat = a.num.number := by
  rw [Fraction.rat, mul_comm]
  apply div_mul_cancel₀
  exact_mod_cast ha

/-- The generated row is the paper's rational row scaled by a nonzero
power of its raw input denominator. No normalization of labels is used. -/
theorem buildEntry_cast {q : ℕ} (a : Fin q → Fraction) (u : Word q)
    (e : Equation q) (j : Option (Unknown q)) (h : (a e.1).valid) :
    ((buildEntry a u e j).value.number : ℚ) =
      ((a e.1).den.number : ℚ)^(q-2) *
        augment (encoderMatrix (physicalLabels a) u) (encoderRhs u) e j := by
  rcases e with ⟨t,v⟩
  by_cases hv : v.1 t = u.2 t
  · cases j <;> simp [buildEntry, computedEntry, zeroS, hv, augment, encoderMatrix, encoderRhs]
  cases j with
  | none =>
    by_cases hu : u = v
    · subst u
      simp [buildEntry, computedEntry, hv, AffineCost.wordEqual_spec, augment, encoderRhs,
        constantEntry]
    · simp [buildEntry, computedEntry, zeroS, hv, hu, AffineCost.wordEqual_spec,
        augment, encoderRhs, constantEntry]
  | some j =>
    rcases j with ⟨w,k⟩ | ⟨s,k⟩
    · by_cases hw : w = v
      · have hp : k.val+1 ≤ q-2 := k.isLt
        simp only [buildEntry, computedEntry, beq_iff_eq, hv, if_false, AffineCost.wordEqual_spec,
          hw, if_true, Signed.mul_number, signedPower_number, Int.cast_mul, Int.cast_pow,
          augment, Matrix.of_apply, Option.elim'_some, encoderMatrix, physicalLabels]
        rw [← den_mul_rat (a t) h, mul_pow]
        calc
          _ = ((a t).den.number : ℚ)^(q-2-(k.val+1)) *
              ((a t).den.number : ℚ)^(k.val+1) * (a t).rat^(k.val+1) := by ring
          _ = _ := by rw [← pow_add, Nat.sub_add_cancel hp]
      · simp [buildEntry, computedEntry, zeroS, hv, hw, AffineCost.wordEqual_spec,
          augment, encoderMatrix]
    · by_cases hs : s = t <;> by_cases hk : encoderBit k v = true <;>
        simp [buildEntry, computedEntry, zeroS, hv, hs, hk, ← encoderBit_spec k v,
          augment, encoderMatrix]


end Reconstruction.BareissPaper
