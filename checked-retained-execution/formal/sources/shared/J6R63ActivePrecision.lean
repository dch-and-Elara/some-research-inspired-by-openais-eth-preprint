import J6R52FreshExteriorWordsFee
import J6ActiveSchedule

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8500000
set_option maxRecDepth 1950
set_option Elab.async false

/-! Compute the real next receiving precision, not the precision word
of a hypothetical future outgoing address.  The inherited p, current
edge count M, and taper width u are finite source words.  The fixed
signed-grid axis selects the paid one-hot scale. -/
namespace J6R63Active
open AOracleMachineTime A1R10 J6R22RootReadout J6R52FreshExterior

def precisionProgram {q : ℕ} (hq : 0<q) (a i : ℕ)
    (base edges taper : J6R15ModeCost.Word q) : Meter (J6R15ModeCost.Word q) :=
  let p := modeWordAsA base
  let m := modeWordAsA edges
  let u := modeWordAsA taper
  let one := constantRegister q [true]
  let three := constantRegister q [true,true]
  let eight := constantRegister q [false,false,false,true]
  let scale := powerRegister q (a-i)
  let slope := timesAddRegister one.result one.result a
  let off := subWord hq u one.result
  let n₀ := mulWord three.result m
  let n := addWord n₀.result off.result
  let h := divideMagnitude n.result u
  let e₀ := mulWord eight.result h.result
  let e := mulWord e₀.result scale.result
  let w₀ := mulWord eight.result m
  let w := mulWord w₀.result slope.result
  let t := addWord e.result w.result
  let r := addWord p t.result
  ⟨aWordAsMode r.result,one.steps+three.steps+eight.steps+scale.steps+slope.steps+
    off.steps+n₀.steps+n.steps+h.steps+e₀.steps+e.steps+w₀.steps+w.steps+t.steps+r.steps+16⟩

def precisionAt (a i p m u : ℕ) : ℕ :=
  J9PrintedSchedule.precision p (J6ActiveSchedule.height m u) (2^(a-i)) m a

theorem precision_program_exact {q : ℕ} (hq : 0<q) (a i : ℕ)
    (base edges taper : J6R15ModeCost.Word q)
    (positive : 0<taper.val)
    (numeratorFits : 3*edges.val+taper.val-1<2^q)
    (outputFits : precisionAt a i base.val edges.val taper.val<2^q) :
    (precisionProgram hq a i base edges taper).result.val =
      precisionAt a i base.val edges.val taper.val := by
  let p := modeWordAsA base
  let m := modeWordAsA edges
  let u := modeWordAsA taper
  let O := (constantRegister q [true]).result
  let T := (constantRegister q [true,true]).result
  let E := (constantRegister q [false,false,false,true]).result
  let A := (powerRegister q (a-i)).result
  let B := (timesAddRegister O O a).result
  let N := (addWord (mulWord T m).result (subWord hq u O).result).result
  let H := (divideMagnitude N u).result
  have rp : wordRead p=(base.val:ZMod (2^q)) := rfl
  have rm : wordRead m=(edges.val:ZMod (2^q)) := rfl
  have ru : wordRead u=(taper.val:ZMod (2^q)) := rfl
  have ro : wordRead O=1 := by norm_num [O,constant_register_read,bitsValue,Bool.toNat]
  have rt : wordRead T=3 := by norm_num [T,constant_register_read,bitsValue,Bool.toNat]
  have re : wordRead E=8 := by norm_num [E,constant_register_read,bitsValue,Bool.toNat]
  have ra : wordRead A=((2^(a-i):ℕ):ZMod (2^q)) := by
    simp only [A,power_register_read,Nat.cast_pow,Nat.cast_ofNat]
  have rb : wordRead B=((a+1:ℕ):ZMod (2^q)) := by
    rw [show wordRead B=wordRead O+(a:ZMod (2^q))*wordRead O from times_add_register_read O O a,ro]
    push_cast
    ring
  have num : wordRead N=((3*edges.val+taper.val-1:ℕ):ZMod (2^q)) := by
    change wordRead (addWord (mulWord T m).result (subWord hq u O).result).result=_
    have h : 1≤3*edges.val+taper.val := by omega
    rw [addWord_read,mulWord_read,subWord_read,rt,rm,ru,ro,Nat.cast_sub h]
    push_cast
    ring
  have nv := exact_nat_of_register_read N numeratorFits num
  have hv : bitsValue H.val=J6ActiveSchedule.height edges.val taper.val := by
    have d := (divide_magnitude_exact N u (show 0<bitsValue u.val from positive)).1
    change bitsValue H.val=_ at d
    rw [nv] at d
    exact d
  have hread : wordRead H=(J6ActiveSchedule.height edges.val taper.val:ZMod (2^q)) := by
    change (bitsValue H.val : ZMod (2^q))=_
    rw [hv]
  change bitsValue ((addWord p (addWord
    (mulWord (mulWord E H).result A).result (mulWord (mulWord E m).result B).result).result).result).val=_
  apply exact_nat_of_register_read _ outputFits
  rw [addWord_read,addWord_read,mulWord_read,mulWord_read,mulWord_read,mulWord_read,
    rp,re,hread,ra,rm,rb]
  unfold precisionAt J9PrintedSchedule.precision
  push_cast
  ring

def precisionFee (a q : ℕ) : ℕ :=
  4*(4*q+4)+(2+a*(wordArithmeticRoof q+5))+
    9*wordArithmeticRoof q+signedDivisionFee q q+16

theorem precision_program_budget {q : ℕ} (hq : 0<q) (a i : ℕ)
    (base edges taper : J6R15ModeCost.Word q) :
    (precisionProgram hq a i base edges taper).steps≤precisionFee a q := by
  let p := modeWordAsA base
  let m := modeWordAsA edges
  let u := modeWordAsA taper
  let O := constantRegister q [true]
  let T := constantRegister q [true,true]
  let E := constantRegister q [false,false,false,true]
  let A := powerRegister q (a-i)
  let B := timesAddRegister O.result O.result a
  let F := subWord hq u O.result
  let N₀ := mulWord T.result m
  let N := addWord N₀.result F.result
  let H := divideMagnitude N.result u
  let X₀ := mulWord E.result H.result
  let X := mulWord X₀.result A.result
  let Y₀ := mulWord E.result m
  let Y := mulWord Y₀.result B.result
  let D := addWord X.result Y.result
  let R := addWord p D.result
  have one : O.steps=4*q+4 := constant_register_fee q _
  have three : T.steps=4*q+4 := constant_register_fee q _
  have eight : E.steps=4*q+4 := constant_register_fee q _
  have scale : A.steps=4*q+4 := power_register_fee q _
  have slope : B.steps≤2+a*(wordArithmeticRoof q+5) :=
    repeated_add_register_fee_le hq _ _ _
  have off : F.steps≤wordArithmeticRoof q := (wordOps q hq).sub_cost _ _
  have mul : N₀.steps≤wordArithmeticRoof q := mul_word_fee_le hq _ _
  have add : N.steps≤wordArithmeticRoof q := add_word_fee_le hq _ _
  have div : H.steps=signedDivisionFee q q := restoring_register_fee _ _
  have b₁ : X₀.steps≤wordArithmeticRoof q := mul_word_fee_le hq _ _
  have b₂ : X.steps≤wordArithmeticRoof q := mul_word_fee_le hq _ _
  have b₃ : Y₀.steps≤wordArithmeticRoof q := mul_word_fee_le hq _ _
  have b₄ : Y.steps≤wordArithmeticRoof q := mul_word_fee_le hq _ _
  have b₅ : D.steps≤wordArithmeticRoof q := add_word_fee_le hq _ _
  have b₆ : R.steps≤wordArithmeticRoof q := add_word_fee_le hq _ _
  change O.steps+T.steps+E.steps+A.steps+B.steps+F.steps+N₀.steps+N.steps+H.steps+
    X₀.steps+X.steps+Y₀.steps+Y.steps+D.steps+R.steps+16≤_
  unfold precisionFee
  omega

#print axioms precision_program_exact
#print axioms precision_program_budget
end J6R63Active

