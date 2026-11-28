import J3R60PublicHeight
import J3R60LiteralBudget

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3900000

/-! Reduced rational bit heights for the original normalization. This
closes the connection between source row coefficients and the actual
integer elimination budget; no hidden bound on normalized data is assumed. -/
namespace J3R60
open V8NativeMessage
open scoped BigOperators

theorem rat_den_mul_value (q : ℚ) : (q.den : ℚ)*q = (q.num : ℚ) := by
  rw [mul_comm]
  exact ((div_eq_iff (Nat.cast_ne_zero.mpr (Rat.den_nz q))).mp
    (Rat.num_div_den q)).symm

theorem height_of_integral_scale {B d : ℕ} {q : ℚ} {a : ℤ}
    (h : (d : ℚ)*q = a) (hp : 0 < d) (ha : a.natAbs ≤ 2^B) (hd : d ≤ 2^B) :
    inputHeight B q := by
  obtain ⟨hq,hn⟩ := N1.normalized_rational_bound q d hp a h
  exact ⟨hn.trans ha,(Nat.le_of_dvd hp hq).trans hd⟩

theorem height_mul {B C : ℕ} {q r : ℚ} (hq : inputHeight B q) (hr : inputHeight C r) :
    inputHeight (B+C) (q*r) := by
  have h : ((q.den*r.den : ℕ) : ℚ)*(q*r) = ((q.num*r.num : ℤ) : ℚ) := by
    simp only [Nat.cast_mul, Int.cast_mul]
    calc
      _ = ((q.den:ℚ)*q)*((r.den:ℚ)*r) := by ring
      _ = _ := by rw [rat_den_mul_value,rat_den_mul_value]
  refine height_of_integral_scale h (Nat.mul_pos q.den_pos r.den_pos) ?_ ?_
  · rw [Int.natAbs_mul,Nat.pow_add]
    exact Nat.mul_le_mul hq.1 hr.1
  · rw [Nat.pow_add]
    exact Nat.mul_le_mul hq.2 hr.2

theorem height_add {B C : ℕ} {q r : ℚ} (hq : inputHeight B q) (hr : inputHeight C r) :
    inputHeight (B+C+1) (q+r) := by
  have h : ((q.den*r.den : ℕ) : ℚ)*(q+r) =
      ((q.num*(r.den:ℤ)+r.num*(q.den:ℤ) : ℤ) : ℚ) := by
    simp only [Nat.cast_mul, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    calc
      _ = ((q.den:ℚ)*q)*(r.den:ℚ)+((r.den:ℚ)*r)*(q.den:ℚ) := by ring
      _ = _ := by rw [rat_den_mul_value,rat_den_mul_value]
  refine height_of_integral_scale h (Nat.mul_pos q.den_pos r.den_pos) ?_ ?_
  · apply (Int.natAbs_add_le ..).trans
    simp only [Int.natAbs_mul,Int.natAbs_natCast]
    have h1 := Nat.mul_le_mul hq.1 hr.2
    have h2 := Nat.mul_le_mul hr.1 hq.2
    rw [Nat.pow_succ,Nat.pow_add]
    rw [mul_comm (2^C) (2^B)] at h2
    simpa only [mul_two] using Nat.add_le_add h1 h2
  · exact (Nat.mul_le_mul hq.2 hr.2).trans
      (by rw [←Nat.pow_add]; exact Nat.pow_le_pow_right (by decide) (Nat.le_succ _))

theorem height_neg {B : ℕ} {q : ℚ} (hq : inputHeight B q) : inputHeight B (-q) := by
  simpa only [inputHeight,Rat.neg_num,Rat.neg_den,Int.natAbs_neg] using hq

theorem height_sub {B C : ℕ} {q r : ℚ} (hq : inputHeight B q) (hr : inputHeight C r) :
    inputHeight (B+C+1) (q-r) := by rw [sub_eq_add_neg]; exact height_add hq (height_neg hr)

theorem height_inv {B : ℕ} {q : ℚ} (hq : inputHeight B q) : inputHeight B q⁻¹ := by
  constructor
  · rw [Rat.num_inv,Int.natAbs_mul,Int.natAbs_natCast,Int.natAbs_sign]
    split
    · exact (Nat.zero_mul _).le.trans (Nat.zero_le _)
    · simpa only [one_mul] using hq.2
  · rw [Rat.den_inv]
    split
    · exact Nat.one_le_two_pow
    · exact hq.1

theorem height_div {B C : ℕ} {q r : ℚ} (hq : inputHeight B q) (hr : inputHeight C r) :
    inputHeight (B+C) (q/r) := by rw [div_eq_mul_inv]; exact height_mul hq (height_inv hr)

theorem height_sum {I : Type*} {B : ℕ} (f : I → ℚ) (h : ∀ i, inputHeight B (f i)) (s : Finset I) :
    inputHeight ((B+1)*s.card) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [inputHeight]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.card_insert_of_notMem hi]
    convert height_add (h i) ih using 1
    rw [Nat.mul_add, Nat.mul_one]
    omega

theorem height_one_sub {B : ℕ} {q : ℚ} (hq : inputHeight B q) :
    inputHeight (B+1) (1-q) := by
  have h : inputHeight 0 (1:ℚ) := by unfold inputHeight; decide
  simpa only [Nat.zero_add] using height_sub h hq

def normHeight (B n : ℕ) := (B+B)+(B+B)+2+((B+(B+1))+1)*n

theorem normalized_equation_height {W : Type*} [Fintype W] {B : ℕ}
    (H h Bk bk : ℚ) (theta der : W → ℚ)
    (hh : inputHeight B H) (hh' : inputHeight B h)
    (hb : inputHeight B Bk) (hb' : inputHeight B bk)
    (ht : ∀ v,inputHeight B (theta v)) (hd : ∀ v,inputHeight B (der v)) :
    (∀ v,inputHeight (normHeight B (Fintype.card W))
      (der v/(theta v*(1-theta v)))) ∧
    inputHeight (normHeight B (Fintype.card W))
      (h/H-bk/Bk+∑ v,der v/(1-theta v)) := by
  have hs := height_sum (fun v=>der v/(1-theta v))
    (fun v=>height_div (hd v) (height_one_sub (ht v))) Finset.univ
  constructor
  · intro v
    refine inputHeight_mono ?_ (height_div (hd v) (height_mul (ht v) (height_one_sub (ht v))))
    unfold normHeight
    omega
  · have ho := height_add (height_sub (height_div hh' hh) (height_div hb' hb)) hs
    simp only [Finset.card_univ] at ho
    convert ho using 1
    unfold normHeight
    omega

theorem inputBits_upper {I : Type*} [Fintype I] {n B : ℕ}
    (A : I → Fin n → ℚ) (b : I → ℚ)
    (hA : ∀ i j,inputHeight B (A i j)) (hb : ∀ i,inputHeight B (b i)) :
    inputBits A b ≤ B := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
  unfold dataMax rationalMagnitude
  apply max_le
  · exact Finset.sup_le (fun p _ => max_le (hA p.1 p.2).1 (hA p.1 p.2).2)
  · exact Finset.sup_le (fun i _ => max_le (hb i).1 (hb i).2)

open J3R38LiteralSingleton
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber
open scoped Classical
noncomputable section

variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J R BP : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

/-- Source-side height of the actual input of `original_J3_actual_budget`.
It follows from the original row coefficient bounds, not a supplied
left inverse, matrix height or received oracle solve. -/
theorem original_J3_source_input_bits (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (hr : 2 ≤ r) (hR : 1 ≤ R) (hfit : 6*R ≤ Q)
    (Aset : Finset (Address W Q))
    (bounds : ∀ a ∈ Aset,N1.RowBound (literalTuple P R hJ Prow a) hreg R BP)
    (cols : Fin (Fintype.card W) ≃ W) (s : W → Bool) :
    inputBits (fun (a : {a // a ∈ Aset}) j=>graphEntry hreg Prow a.val (cols j))
      (fun a=>normalize P R hJ Prow a.val (rawJet P R hJ Prow a.val s)) ≤
      normHeight (publicHeight W R Q BP) (Fintype.card W) := by
  have hp (a : {a // a ∈ Aset}) := original_J3_primitives_height P Prow
    hJ hr hR hfit a.val s (bounds _ a.property)
  apply inputBits_upper
  · intro a j
    obtain ⟨h0,h1,hb0,hb1,ht,hd⟩ := hp a
    exact (normalized_equation_height _ _ _ _ _ _ h0 h1 hb0 hb1 ht hd).1 (cols j)
  · intro a
    obtain ⟨h0,h1,hb0,hb1,ht,hd⟩ := hp a
    exact (normalized_equation_height _ _ _ _ _ _ h0 h1 hb0 hb1 ht hd).2

#print axioms height_mul
#print axioms height_add
#print axioms height_div
#print axioms height_sum
#print axioms normalized_equation_height
#print axioms inputBits_upper
#print axioms original_J3_source_input_bits

end
end J3R60
