
import J6R22RootReadoutDivide
import J6IntegerRootTrace

/-! The signed greedy root does a checked physical power and a
bit-serial comparison at each candidate. Its scratch width is explicit
and no power comparisons, integer root, or integer division are oracles. -/
namespace J6R22RootReadout
open A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape AAcquisitionCost
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11000000

def unsignedLE {w : ℕ} (a b : A1R10.Word w) : Bool :=
  !(rippleBorrow b.val a.val false).2

theorem unsigned_le_exact {w : ℕ} (a b : A1R10.Word w) :
    unsignedLE a b=true ↔ bitsValue a.val≤bitsValue b.val := by
  unfold unsignedLE
  rw [Bool.not_eq_true',Bool.eq_false_iff]
  exact (not_congr (unsigned_borrow_equiv b a)).trans Nat.not_lt

theorem add_nat_word {w : ℕ} (a b : A1R10.Word w)
    (small : bitsValue a.val+bitsValue b.val<2^w) :
    bitsValue (addWord a b).result.val=bitsValue a.val+bitsValue b.val := by
  rw [← word_value_of_read,addWord_read]
  change (((bitsValue a.val:ℕ):ZMod (2^w))+((bitsValue b.val:ℕ):ZMod (2^w))).val=_
  rw [← Nat.cast_add,ZMod.val_natCast_of_lt small]

theorem power_nat_word {w : ℕ} (hw : 0<w) (a : A1R10.Word w) (clock : List Unit)
    (small : (bitsValue a.val)^clock.length<2^w) :
    bitsValue (powerMod a clock).result.val=(bitsValue a.val)^clock.length := by
  rw [← word_value_of_read,(power_mod_exact hw a clock).1]
  change (((bitsValue a.val:ℕ):ZMod (2^w))^clock.length).val=_
  rw [← Nat.cast_pow,ZMod.val_natCast_of_lt small]

def rootProbeFee (w e maxDepth : ℕ) :=
  32*(w+1)^2+e*wordMulFee w+50*(w+maxDepth+1)

def wordRootSearch {w : ℕ} (hw : 0<w) (target : A1R10.Word w) (exp : List Unit) :
    List Unit→A1R10.Word w→Meter (A1R10.Word w)
  | [],accum => ⟨accum,2⟩
  | _::suffix,accum =>
    let candidate := addWord accum (dyadicWord w suffix.length)
    let pow := powerMod candidate.result exp
    let next := if unsignedLE pow.result target then candidate.result else accum
    let rest := wordRootSearch hw target exp suffix next
    ⟨rest.result,rest.steps+candidate.steps+pow.steps+25*w+4*suffix.length+12⟩

theorem word_root_search_exact {w b : ℕ} (hw : 0<w) (hb : b≤w)
    (target : A1R10.Word w) (exp digs : List Unit) (accum : A1R10.Word w)
    (hcap : b*exp.length<w)
    (fits : bitsValue accum.val+2^digs.length≤2^b) :
    bitsValue (wordRootSearch hw target exp digs accum).result.val =
      (J6IntegerRoot.recoverNat (fun y=>y^exp.length) (bitsValue target.val)
        digs.length (bitsValue accum.val)).1 := by
  induction digs generalizing accum with
  | nil => rfl
  | cons u ds ih =>
    let q := 2^ds.length
    let y := bitsValue accum.val
    let C := addWord accum (dyadicWord w ds.length)
    have I : y+2*q≤2^b := by simpa only [List.length_cons,pow_succ,q,y,Nat.mul_comm] using fits
    have qp : 0<q := by unfold q; positivity
    have pSmall : y+q<2^b := by omega
    have powFit : (2:ℕ)^b≤2^w := Nat.pow_le_pow_right (by decide) hb
    have l : ds.length<w := by
      by_contra h
      have alt : (2:ℕ)^w≤q := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt h)
      omega
    have d : bitsValue (dyadicWord w ds.length).val=q := by
      change bitsValue (dyadicBits w ds.length)=_
      rw [dyadicBits_value,if_pos l]
    have c : bitsValue C.result.val=y+q := by
      change bitsValue (addWord accum (dyadicWord w ds.length)).result.val=_
      exact (add_nat_word _ _ (by rw [d]; exact pSmall.trans_le powFit)).trans (by rw [d])
    have powBound : (bitsValue C.result.val)^exp.length<2^w := by
      rw [c]
      calc
        _ ≤ (2^b)^exp.length := Nat.pow_le_pow_left pSmall.le _
        _ = 2^(b*exp.length) := (pow_mul 2 _ _).symm
        _ < _ := Nat.pow_lt_pow_right (by decide) hcap
    let power := powerMod C.result exp
    have pw : bitsValue power.result.val=(y+q)^exp.length :=
      (power_nat_word hw C.result exp powBound).trans (congrArg (fun n=>n^exp.length) c)
    have comp : unsignedLE power.result target=true ↔ (y+q)^exp.length≤bitsValue target.val := by
      rw [unsigned_le_exact,pw]
    change bitsValue (wordRootSearch hw target exp ds (if unsignedLE power.result target then C.result else accum)).result.val =
      (J6IntegerRoot.recoverNat _ _ ds.length
        (if (y+q)^exp.length≤bitsValue target.val then y+q else y)).1
    by_cases h : (y+q)^exp.length≤bitsValue target.val
    · rw [if_pos (comp.mpr h),if_pos h]
      have f : bitsValue C.result.val+2^ds.length≤2^b := by rw [c]; change y+q+q≤_; omega
      rw [ih C.result f,c]
    · rw [if_neg (fun ht=>h (comp.mp ht)),if_neg h]
      exact ih accum (by change y+q≤_; omega)

theorem word_root_search_cost {w : ℕ} (hw : 0<w)
    (target : A1R10.Word w) (exp digs : List Unit) (accum : A1R10.Word w)
    (cap : ℕ) (hc : digs.length≤cap) :
    (wordRootSearch hw target exp digs accum).steps≤2+digs.length*rootProbeFee w exp.length cap := by
  induction digs generalizing accum with
  | nil => simp [wordRootSearch]
  | cons u ds ih =>
    let C := addWord accum (dyadicWord w ds.length)
    let P := powerMod C.result exp
    let nxt := if unsignedLE P.result target then C.result else accum
    have h0 : ds.length≤cap := by simpa only [List.length_cons] using (Nat.le_of_succ_le hc)
    have q := ih nxt h0
    have cc := (wordOps w hw).add_cost accum (dyadicWord w ds.length)
    change C.steps≤32*(w+1)^2 at cc
    have cp := (power_mod_exact hw C.result exp).2
    change P.steps≤3*w+4+exp.length*wordMulFee w at cp
    change (wordRootSearch hw target exp ds nxt).steps+C.steps+P.steps+25*w+4*ds.length+12≤
      2+(ds.length+1)*rootProbeFee w exp.length cap
    rw [Nat.add_mul,one_mul]
    unfold rootProbeFee at q ⊢
    omega

/-- The scratch width depends only on public input width and exponent;
the target register is widened, not read as an unpriced Nat. -/
def signedRootWord {p w : ℕ} (hw : 0<w) (x : SignedMagnitude p)
    (exp digs : List Unit) : Meter (SignedMagnitude w) :=
  let recv := asLowWord w x.magnitude.val
  let s := wordRootSearch hw recv exp digs (wordZero w)
  ⟨⟨x.negative,s.result⟩,s.steps+8*w+8⟩

theorem signed_root_word_exact {p w : ℕ} (hw : 0<w) (hpw : p≤w)
    (x : SignedMagnitude p) (exp digs : List Unit) (hd : digs.length=p)
    (hcap : p*exp.length<w) (root : ℤ) (odd : Odd exp.length)
    (hr : x.value=root^exp.length) (fit : root.natAbs<2^p) :
    (signedRootWord hw x exp digs).result.value=root ∧
      (signedRootWord hw x exp digs).steps≤8*w+10+p*rootProbeFee w exp.length p := by
  let recv := asLowWord w x.magnitude.val
  have low : bitsValue recv.val=bitsValue x.magnitude.val := by
    change bitsValue (lowBits w x.magnitude.val)=_
    rw [lowBits_value,Nat.mod_eq_of_lt ((read_bits_bound x.magnitude).trans_le
      (Nat.pow_le_pow_right (by decide) hpw))]
  have zero : bitsValue (wordZero w).val=0 := by
    rw [← word_value_of_read]
    change ((wordOps w hw).read (wordOps w hw).zero).val=0
    rw [(wordOps w hw).zero_read,ZMod.val_zero]
  have hfit : bitsValue (wordZero w).val+2^digs.length≤2^p := by rw [zero,hd,zero_add]
  have exactSearch := word_root_search_exact hw hpw recv exp digs (wordZero w) hcap hfit
  rw [low,zero,hd] at exactSearch
  have ha : x.value.natAbs=bitsValue x.magnitude.val := by
    unfold SignedMagnitude.value signedDenote
    cases x.negative <;> simp
  have hmain : (J6IntegerRoot.recoverNat (fun y=>y^exp.length) (bitsValue x.magnitude.val) p 0).1 =
      root.natAbs := by
    rw [← ha,hr,Int.natAbs_pow]
    refine J6IntegerRoot.recoverNat_exact _ ?_ _ _ _ (Nat.zero_le _) (by simp [fit])
    intro a b h
    have hZ : (a:ℤ)<b := by exact_mod_cast h
    change a^exp.length<b^exp.length
    exact_mod_cast (show (a:ℤ)^exp.length<(b:ℤ)^exp.length from odd.strictMono_pow hZ)
  constructor
  · have hN : bitsValue (wordRootSearch hw recv exp digs (wordZero w)).result.val=root.natAbs :=
      exactSearch.trans hmain
    change (if x.negative then -(bitsValue (wordRootSearch hw recv exp digs (wordZero w)).result.val:ℤ)
      else bitsValue (wordRootSearch hw recv exp digs (wordZero w)).result.val)=root
    rw [hN]
    have signEq : 0≤x.value ↔ 0≤root := by
      rw [hr]
      have hn : exp.length≠0 := by obtain ⟨z,h⟩ := odd; omega
      simpa only [zero_pow hn] using (odd.strictMono_pow (R:=ℤ)).le_iff_le (a:=0) (b:=root)
    cases signBit : x.negative with
    | false =>
      have hx : 0≤x.value := by simp [SignedMagnitude.value,signedDenote,signBit]
      simp only [Bool.false_eq_true,if_false]
      exact Int.natAbs_of_nonneg (signEq.mp hx)
    | true =>
      simp only [if_true]
      by_cases hz : root=0
      · simp [hz]
      · have hx : x.value≤0 := by
          simp [SignedMagnitude.value,signedDenote,signBit]
        have hnr : root≤0 := by
          by_contra H
          have hp0 : 0<root := lt_of_not_ge H
          have hp1 : 0<root^exp.length := pow_pos hp0 _
          rw [hr] at hx
          omega
        have e := Int.natAbs_of_nonneg (neg_nonneg.mpr hnr)
        rw [Int.natAbs_neg] at e
        linarith
  · have h := word_root_search_cost hw recv exp digs (wordZero w) p (by rw [hd])
    change (wordRootSearch hw recv exp digs (wordZero w)).steps+8*w+8≤_
    rw [hd] at h
    omega

#print axioms unsigned_le_exact
#print axioms add_nat_word
#print axioms power_nat_word
#print axioms word_root_search_exact
#print axioms word_root_search_cost
#print axioms signed_root_word_exact
end J6R22RootReadout
