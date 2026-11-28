
import A1R12Words
import AAcquisitionCostDivision
import Mathlib.Data.ZMod.ValMinAbs

/-! Appendix D's signed readout starts from a physical p-bit residue.
Modular denominator clearing and the centered lift are bit programs,
not field division or arbitrary-precision integer arithmetic. -/
namespace J6R22RootReadout
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul
open AOracleCoordinates A1R10 A1R12 AAcquisitionCost
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5600000

theorem little_endian_same (xs : List Bool) : wordNat xs=bitsValue xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [wordNat,bitsValue,bitNat,ih]

theorem word_value_of_read {p : ℕ} (a : A1R10.Word p) :
    (wordRead a).val=bitsValue a.val := by
  change ((bitsValue a.val:ℕ):ZMod (2^p)).val=_
  apply ZMod.val_natCast_of_lt
  have h := wordNat_lt_width a.val
  rwa [little_endian_same,a.property] at h

theorem read_bits_bound {p : ℕ} (a : A1R10.Word p) :
    bitsValue a.val<2^p := by
  have h := wordNat_lt_width a.val
  rwa [little_endian_same,a.property] at h

def wordMulFee (p : ℕ) := 32*(p+1)^2+2*p+5

def powerMod {p : ℕ} (a : A1R10.Word p) : List Unit→Meter (A1R10.Word p)
  | [] => ⟨wordOne p,3*p+4⟩
  | _::ds =>
    let s := powerMod a ds
    let t := mulWord s.result a
    ⟨t.result,s.steps+t.steps+2*p+5⟩

theorem power_mod_exact {p : ℕ} (hp : 0<p)
    (a : A1R10.Word p) (exp : List Unit) :
    wordRead (powerMod a exp).result=(wordRead a)^exp.length ∧
      (powerMod a exp).steps≤3*p+4+exp.length*wordMulFee p := by
  induction exp with
  | nil => simp [powerMod,wordOne_read p hp]
  | cons u e ih =>
    let s := powerMod a e
    constructor
    · simp only [powerMod,mulWord_read,List.length_cons,pow_succ,ih.1]
    · have cost := (wordOps p hp).mul_cost s.result a
      change (mulWord s.result a).steps≤32*(p+1)^2 at cost
      have hc := ih.2
      change s.steps≤3*p+4+e.length*wordMulFee p at hc
      change s.steps+(mulWord s.result a).steps+2*p+5≤3*p+4+(e.length+1)*wordMulFee p
      rw [Nat.add_mul,one_mul]
      unfold wordMulFee at hc ⊢
      omega

def clearMod {p : ℕ} (den value : A1R10.Word p) (N : List Unit) : Meter (A1R10.Word p) :=
  let d := powerMod den N
  let z := mulWord d.result value
  ⟨z.result,d.steps+z.steps+2*p+5⟩

theorem clear_mod_exact {p : ℕ} (hp : 0<p)
    (den value : A1R10.Word p) (N : List Unit) :
    wordRead (clearMod den value N).result=(wordRead den)^N.length*wordRead value ∧
      (clearMod den value N).steps≤3*p+4+(N.length+1)*wordMulFee p := by
  let s := powerMod den N
  have h := power_mod_exact hp den N
  constructor
  · simp only [clearMod,mulWord_read,h.1]
  · have cost := (wordOps p hp).mul_cost s.result value
    change (mulWord s.result value).steps≤32*(p+1)^2 at cost
    have hc := h.2
    change s.steps≤3*p+4+N.length*wordMulFee p at hc
    change s.steps+(mulWord s.result value).steps+2*p+5≤3*p+4+(N.length+1)*wordMulFee p
    rw [Nat.add_mul,one_mul]
    unfold wordMulFee at hc ⊢
    omega

theorem unsigned_borrow_equiv {p : ℕ} (a b : A1R10.Word p) :
    (rippleBorrow a.val b.val false).2=true ↔ bitsValue a.val<bitsValue b.val := by
  let r := rippleBorrow a.val b.val false
  have h := rippleBorrow_value a.val b.val false (a.property.trans b.property.symm)
  change wordNat a.val+2^a.val.length*bitNat r.2=wordNat b.val+bitNat false+wordNat r.1 at h
  have rlen := rippleBorrow_length a.val b.val false (a.property.trans b.property.symm)
  change r.1.length=a.val.length at rlen
  have lt := wordNat_lt_width r.1
  rw [rlen,a.property] at lt
  change r.2=true ↔ _
  rw [← little_endian_same a.val,← little_endian_same b.val]
  rw [a.property] at h
  cases z : r.2 <;> simp [z,bitNat] at h ⊢ <;> omega

structure SignedMagnitude (p : ℕ) where
  negative : Bool
  magnitude : A1R10.Word p

def SignedMagnitude.value {p : ℕ} (v : SignedMagnitude p) : ℤ :=
  signedDenote v.negative v.magnitude.val

def centered {p : ℕ} (hp : 0<p) (z : A1R10.Word p) : Meter (SignedMagnitude p) :=
  let half := dyadicWord p (p-1)
  let neg := (rippleBorrow half.val z.val false).2
  let abs := wordSign hp neg z
  ⟨⟨neg,abs.result⟩,abs.steps+20*p+8⟩

theorem half_bits {p : ℕ} (hp : 0<p) :
    bitsValue (dyadicWord p (p-1)).val=2^p/2 := by
  change bitsValue (dyadicBits p (p-1))=_
  rw [dyadicBits_value,if_pos (by omega)]
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  simp [pow_succ]

theorem centered_exact {p : ℕ} (hp : 0<p) (z : A1R10.Word p) :
    (centered hp z).result.value=(wordRead z).valMinAbs ∧
      (centered hp z).steps≤35*p+10 := by
  letI : NeZero (2^p:ℕ) := ⟨by positivity⟩
  let h := dyadicWord p (p-1)
  let sign := (rippleBorrow h.val z.val false).2
  let W := wordSign hp sign z
  have comp := unsigned_borrow_equiv h z
  change sign=true ↔ bitsValue h.val<bitsValue z.val at comp
  rw [half_bits hp,← word_value_of_read z] at comp
  have ws := wordSign_exact hp sign z
  have wcost : W.steps≤15*p+2 := ws.2
  change signedDenote sign W.result.val=(wordRead z).valMinAbs ∧ W.steps+20*p+8≤35*p+10
  refine ⟨?_,by omega⟩
  rw [ZMod.valMinAbs_def_pos]
  by_cases h₀ : (wordRead z).val≤2^p/2
  · have sn : sign=false := Bool.eq_false_of_not_eq_true (fun hs => (Nat.not_lt_of_ge h₀) (comp.mp hs))
    rw [if_pos h₀,signedDenote,sn]
    simp only [Bool.false_eq_true,if_false]
    have eq : wordRead W.result=wordRead z := by 
      simpa only [W,sn,Bool.false_eq_true,if_false] using ws.1
    rw [← word_value_of_read W.result,eq]
  · have above : 2^p/2<(wordRead z).val := Nat.lt_of_not_ge h₀
    have sn := comp.mpr above
    have nz : wordRead z≠0 := by
      intro eq
      rw [eq,ZMod.val_zero] at above
      exact Nat.not_lt_zero _ above
    letI : NeZero (wordRead z) := ⟨nz⟩
    have eq : wordRead W.result= -wordRead z := by simpa only [W,sn,if_true] using ws.1
    rw [if_neg h₀,signedDenote,sn]
    change -(bitsValue W.result.val:ℤ)=(wordRead z).val-((2^p:ℕ):ℤ)
    rw [← word_value_of_read W.result,eq,ZMod.val_neg_of_ne_zero]
    have hlt := (wordRead z).val_lt
    rw [Nat.cast_sub hlt.le]
    ring

def clearAndCenter {p : ℕ} (hp : 0<p) (den z : A1R10.Word p) (N : List Unit) :
    Meter (SignedMagnitude p) :=
  let c := clearMod den z N
  let r := centered hp c.result
  ⟨r.result,c.steps+r.steps+2⟩

theorem clear_and_center_exact {p : ℕ} (hp : 0<p)
    (den z : A1R10.Word p) (N : List Unit) :
    (clearAndCenter hp den z N).result.value=((wordRead den)^N.length*wordRead z).valMinAbs ∧
    (clearAndCenter hp den z N).steps≤38*p+16+(N.length+1)*wordMulFee p := by
  obtain ⟨h,k⟩ := clear_mod_exact hp den z N
  obtain ⟨s,t⟩ := centered_exact hp (clearMod den z N).result
  constructor
  · unfold clearAndCenter
    rw [s,h]
  · change (clearMod den z N).steps+(centered hp (clearMod den z N).result).steps+2≤_
    omega

#print axioms word_value_of_read
#print axioms power_mod_exact
#print axioms clear_mod_exact
#print axioms unsigned_borrow_equiv
#print axioms centered_exact
#print axioms clear_and_center_exact
end J6R22RootReadout
