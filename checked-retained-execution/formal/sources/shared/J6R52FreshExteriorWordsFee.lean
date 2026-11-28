import J6R52FreshExteriorWordsComputed

/-! Finite tape cost for the printed root precision and its copies.
The public printed mesh fixes the loop lengths; arrays or precomputed
integer precision are not supplied as operands. -/
namespace J6R52FreshExterior
open J6Mesh J6R19Retained J6R22RootReadout A1R10
open AOracleMachineTime AOracleMachineTimeTape AAcquisitionCost
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12500000

def wordArithmeticRoof (q : ℕ) : ℕ := 32*(q+1)^2

theorem constant_register_fee (q : ℕ) (raw : List Bool) :
    (constantRegister q raw).steps=4*q+4 := by
  change (scanWidth q raw).steps+3=_
  rw [(scanWidth_exact q raw).2]

theorem power_register_fee (q k : ℕ) :
    (powerRegister q k).steps=4*q+4 := by
  change (emitOneHot q k).steps+3=_
  rw [(emitted_one_hot_exact q k).2]

theorem add_word_fee_le {q : ℕ} (hq : 0<q) (a b : A1R10.Word q) :
    (addWord a b).steps≤wordArithmeticRoof q :=
  (wordOps q hq).add_cost a b

theorem mul_word_fee_le {q : ℕ} (hq : 0<q) (a b : A1R10.Word q) :
    (mulWord a b).steps≤wordArithmeticRoof q :=
  (wordOps q hq).mul_cost a b

theorem repeated_add_register_fee_le {q : ℕ} (hq : 0<q)
    (x y : A1R10.Word q) (k : ℕ) :
    (timesAddRegister x y k).steps≤2+k*(wordArithmeticRoof q+5) := by
  induction k with
  | zero => simp [timesAddRegister]
  | succ k ih =>
    dsimp only [timesAddRegister]
    have h := add_word_fee_le hq (timesAddRegister x y k).result y
    rw [Nat.succ_mul]
    omega

def printedGeometryFee (m q : ℕ) : ℕ :=
  7*(4*q+4)+3*(2+b m*(wordArithmeticRoof q+5))+12

theorem printed_geometry_fee_le (m q : ℕ) (hq : 0<q) :
    (printedGeometryRegisters m q).steps≤printedGeometryFee m q := by
  let z := constantRegister q []
  let o := constantRegister q [true]
  let t := constantRegister q [true,true]
  let f := constantRegister q [false,false,true]
  let e := constantRegister q [false,false,false,true]
  let Q := timesAddRegister z.result f.result (b m)
  let R := timesAddRegister t.result f.result (b m-1)
  let S := timesAddRegister o.result e.result (b m)
  have hQ : Q.steps≤2+b m*(wordArithmeticRoof q+5) :=
    repeated_add_register_fee_le hq z.result f.result _
  have hR : R.steps≤2+b m*(wordArithmeticRoof q+5) :=
    (repeated_add_register_fee_le hq t.result f.result _).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le (b m) 1)) 2)
  have hS : S.steps≤2+b m*(wordArithmeticRoof q+5) :=
    repeated_add_register_fee_le hq o.result e.result _
  change (constantRegister q []).steps+(constantRegister q [true]).steps+
    (constantRegister q [true,true]).steps+(constantRegister q [false,false,true]).steps+
    (constantRegister q [false,false,false,true]).steps+Q.steps+R.steps+S.steps+
    (powerRegister q (lambda m)).steps+(powerRegister q (a m)).steps+12≤_
  simp only [constant_register_fee,power_register_fee,printedGeometryFee]
  omega

theorem restoring_register_fee {q : ℕ} (x d : A1R10.Word q) :
    (divideMagnitude x d).steps=signedDivisionFee q q := by
  change 16*divisionSchedule x.val.reverse d.val+3*x.val.length+3*d.val.length+8=_
  simp only [divisionSchedule,List.length_reverse,x.property,d.property,signedDivisionFee]
  ring

def precisionFromBaseFee (m q : ℕ) : ℕ :=
  printedGeometryFee m q+8*wordArithmeticRoof q+signedDivisionFee q q+16

theorem precision_from_base_fee_le {q : ℕ} (m : ℕ)
    (hq : 0<q) (base : A1R10.Word q) :
    (precisionFromBaseWord m base).steps≤precisionFromBaseFee m q := by
  let G := printedGeometryRegisters m q
  let N₀ := mulWord G.result.three G.result.whole
  let N := addWord N₀.result G.result.offset
  let H := divideMagnitude N.result G.result.divisor
  let A₀ := mulWord G.result.eight H.result
  let A := mulWord A₀.result G.result.length
  let B₀ := mulWord G.result.eight G.result.whole
  let B := mulWord B₀.result G.result.slope
  let T := addWord A.result B.result
  let R := addWord base T.result
  have hG : G.steps≤printedGeometryFee m q := printed_geometry_fee_le m q hq
  have hH : H.steps=signedDivisionFee q q := restoring_register_fee N.result G.result.divisor
  have hN₀ : N₀.steps≤wordArithmeticRoof q := mul_word_fee_le hq _ _
  have hN : N.steps≤wordArithmeticRoof q := add_word_fee_le hq _ _
  have hA₀ : A₀.steps≤wordArithmeticRoof q := mul_word_fee_le hq _ _
  have hA : A.steps≤wordArithmeticRoof q := mul_word_fee_le hq _ _
  have hB₀ : B₀.steps≤wordArithmeticRoof q := mul_word_fee_le hq _ _
  have hB : B.steps≤wordArithmeticRoof q := mul_word_fee_le hq _ _
  have hT : T.steps≤wordArithmeticRoof q := add_word_fee_le hq _ _
  have hR : R.steps≤wordArithmeticRoof q := add_word_fee_le hq _ _
  change G.steps+N₀.steps+N.steps+H.steps+A₀.steps+A.steps+B₀.steps+B.steps+T.steps+R.steps+16≤_
  unfold precisionFromBaseFee
  omega

theorem computed_exterior_registers_fee_le {q : ℕ} (m prec : ℕ)
    (hq : 0<q) (base : J6R15ModeCost.Word q) :
    (computeExteriorRegisters m prec base).steps≤
      precisionFromBaseFee m q+exteriorRegistersFee q q prec+4 := by
  let P := precisionFromBaseWord m (modeWordAsA base)
  let C := makeCopyWord m q
  have hP : P.steps≤precisionFromBaseFee m q := precision_from_base_fee_le m hq (modeWordAsA base)
  have hC : C.steps=4*q+4 := by
    change (emitOneHot q (524184*b m)).steps+3=_
    rw [(emitted_one_hot_exact q _).2]
  have hR (w : ℕ) : (retainAtWidth w (aWordAsMode P.result)).steps=2*q+4*w+5 := by
    change (scanWidth w (aWordAsMode P.result).bits).steps+2*q+4=_
    rw [(scanWidth_exact w _).2]
    omega
  change P.steps+(C.steps+(retainAtWidth q (aWordAsMode P.result)).steps+
    (retainAtWidth prec (aWordAsMode P.result)).steps+8)+4≤_
  rw [hC,hR,hR,exteriorRegistersFee]
  omega

#print axioms constant_register_fee
#print axioms power_register_fee
#print axioms add_word_fee_le
#print axioms mul_word_fee_le
#print axioms repeated_add_register_fee_le
#print axioms printed_geometry_fee_le
#print axioms restoring_register_fee
#print axioms precision_from_base_fee_le
#print axioms computed_exterior_registers_fee_le
end J6R52FreshExterior

