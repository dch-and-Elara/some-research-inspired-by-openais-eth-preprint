import J6R63ActivePrecision
import J6R22ActiveScaled

/-! The actual height register shared by the base centre roster.
This is the literal head of the R63 precision program, stopping at the
restoring divide instead of recomputing the height for each node. -/
namespace J6R68ActiveInputs
open AOracleMachineTime A1R10 J6R22RootReadout J6R52FreshExterior J6ActiveSchedule J6R22Active HermiteLoss

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10000000
set_option maxRecDepth 2500
set_option Elab.async false

def heightWord {q : ℕ} (hq : 0<q) (edge taper : J6R15ModeCost.Word q) :
    Meter (Word q) :=
  let E := modeWordAsA edge
  let U := modeWordAsA taper
  let o := constantRegister q [true]
  let t := constantRegister q [true,true]
  let extra := subWord hq U o.result
  let triple := mulWord t.result E
  let sum := addWord triple.result extra.result
  let div := divideMagnitude sum.result U
  ⟨div.result,o.steps+t.steps+extra.steps+triple.steps+sum.steps+div.steps+8⟩

def heightWordRoof (q : ℕ) : ℕ :=
  2*(4*q+4)+3*wordArithmeticRoof q+signedDivisionFee q q+8

theorem actual_height_word_exact {q : ℕ} (hq : 0<q)
    (edge taper : J6R15ModeCost.Word q)
    (pos : 0<taper.val) (fit : 3*edge.val+taper.val-1<2^q) :
    bitsValue (heightWord hq edge taper).result.val=height edge.val taper.val := by
  let E := modeWordAsA edge
  let U := modeWordAsA taper
  let O := (constantRegister q [true]).result
  let T := (constantRegister q [true,true]).result
  let N := (addWord (mulWord T E).result (subWord hq U O).result).result
  have rm : wordRead E=(edge.val:ZMod (2^q)) := rfl
  have ru : wordRead U=(taper.val:ZMod (2^q)) := rfl
  have ro : wordRead O=1 := by norm_num [O,constant_register_read,bitsValue,Bool.toNat]
  have rt : wordRead T=3 := by norm_num [T,constant_register_read,bitsValue,Bool.toNat]
  have num : wordRead N=((3*edge.val+taper.val-1:ℕ):ZMod (2^q)) := by
    change wordRead (addWord (mulWord T E).result (subWord hq U O).result).result=_
    have lower : 1 ≤ 3*edge.val+taper.val := by omega
    rw [addWord_read,mulWord_read,subWord_read,rt,rm,ru,ro,Nat.cast_sub lower]
    push_cast
    ring
  have nv := exact_nat_of_register_read N fit num
  have hv := (divide_magnitude_exact N U (show 0<bitsValue U.val from pos)).1
  change bitsValue (divideMagnitude N U).result.val=bitsValue N.val/taper.val at hv
  rw [nv] at hv
  exact hv

theorem actual_height_word_fee {q : ℕ} (hq : 0<q)
    (edge taper : J6R15ModeCost.Word q) :
    (heightWord hq edge taper).steps ≤ heightWordRoof q := by
  let E := modeWordAsA edge
  let U := modeWordAsA taper
  let o := constantRegister q [true]
  let t := constantRegister q [true,true]
  let extra := subWord hq U o.result
  let triple := mulWord t.result E
  let sum := addWord triple.result extra.result
  let div := divideMagnitude sum.result U
  have ho : o.steps=4*q+4 := constant_register_fee q _
  have ht : t.steps=4*q+4 := constant_register_fee q _
  have h₁ : extra.steps ≤ wordArithmeticRoof q := (wordOps q hq).sub_cost _ _
  have h₂ : triple.steps ≤ wordArithmeticRoof q := mul_word_fee_le hq _ _
  have h₃ : sum.steps ≤ wordArithmeticRoof q := add_word_fee_le hq _ _
  have h₄ : div.steps=signedDivisionFee q q := restoring_register_fee _ _
  change o.steps+t.steps+extra.steps+triple.steps+sum.steps+div.steps+8 ≤ _
  unfold heightWordRoof
  omega


/-- One paid common high-precision margin, from the same height and
edge words. It is not an external larger precision selected for free. -/
def commonLossWord {q : ℕ} (a : ℕ) (edge h : Word q) : Meter (Word q) :=
  let one := constantRegister q [true]
  let four := constantRegister q [false,false,true]
  let six := constantRegister q [false,true,true]
  let scale := powerRegister q a
  let slope := timesAddRegister one.result one.result a
  let s := mulWord six.result h
  let c₁ := mulWord s.result scale.result
  let w := mulWord four.result edge
  let c₂ := mulWord w.result slope.result
  let out := addWord c₁.result c₂.result
  ⟨out.result,one.steps+four.steps+six.steps+scale.steps+slope.steps+
    s.steps+c₁.steps+w.steps+c₂.steps+out.steps+11⟩

def commonLossWordRoof (a q : ℕ) : ℕ :=
  4*(4*q+4)+(2+a*(wordArithmeticRoof q+5))+5*wordArithmeticRoof q+11

theorem literal_common_loss_word_exact {q a M u : ℕ} (edge h : Word q)
    (edgeMeaning : bitsValue edge.val=M) (heightMeaning : bitsValue h.val=height M u)
    (fit : commonLoss a M u<2^q) :
    bitsValue (commonLossWord a edge h).result.val=commonLoss a M u := by
  let O := (constantRegister q [true]).result
  let F := (constantRegister q [false,false,true]).result
  let X := (constantRegister q [false,true,true]).result
  let S := (powerRegister q a).result
  let B := (timesAddRegister O O a).result
  have he : wordRead edge=(M:ZMod (2^q)) := by
    change (bitsValue edge.val:ZMod (2^q))=_
    rw [edgeMeaning]
  have hh : wordRead h=(height M u:ZMod (2^q)) := by
    change (bitsValue h.val:ZMod (2^q))=_
    rw [heightMeaning]
  have ro : wordRead O=1 := by norm_num [O,constant_register_read,bitsValue,Bool.toNat]
  have rf : wordRead F=4 := by norm_num [F,constant_register_read,bitsValue,Bool.toNat]
  have rx : wordRead X=6 := by norm_num [X,constant_register_read,bitsValue,Bool.toNat]
  have rs : wordRead S=((2^a:ℕ):ZMod (2^q)) := by
    simp only [S,power_register_read,Nat.cast_pow,Nat.cast_ofNat]
  have rb : wordRead B=((a+1:ℕ):ZMod (2^q)) := by
    rw [show wordRead B=wordRead O+(a:ZMod (2^q))*wordRead O from
      times_add_register_read O O a,ro]
    push_cast
    ring
  change bitsValue (addWord (mulWord (mulWord X h).result S).result
    (mulWord (mulWord F edge).result B).result).result.val=_
  apply exact_nat_of_register_read _ fit
  rw [addWord_read,mulWord_read,mulWord_read,mulWord_read,mulWord_read,he,hh,rf,rx,rs,rb]
  unfold commonLoss sourceH height
  push_cast
  ring

theorem literal_common_loss_word_fee {q : ℕ} (hq : 0<q) (a : ℕ) (edge h : Word q) :
    (commonLossWord a edge h).steps ≤ commonLossWordRoof a q := by
  let O := constantRegister q [true]
  let F := constantRegister q [false,false,true]
  let X := constantRegister q [false,true,true]
  let S := powerRegister q a
  let B := timesAddRegister O.result O.result a
  let s := mulWord X.result h
  let c₁ := mulWord s.result S.result
  let w := mulWord F.result edge
  let c₂ := mulWord w.result B.result
  let ad := addWord c₁.result c₂.result
  have ho : O.steps=4*q+4 := constant_register_fee q _
  have hf : F.steps=4*q+4 := constant_register_fee q _
  have hx : X.steps=4*q+4 := constant_register_fee q _
  have hs : S.steps=4*q+4 := power_register_fee q _
  have hb : B.steps ≤ 2+a*(wordArithmeticRoof q+5) := repeated_add_register_fee_le hq _ _ _
  have u : s.steps ≤ wordArithmeticRoof q := mul_word_fee_le hq _ _
  have v : c₁.steps ≤ wordArithmeticRoof q := mul_word_fee_le hq _ _
  have w₁ : w.steps ≤ wordArithmeticRoof q := mul_word_fee_le hq _ _
  have w₂ : c₂.steps ≤ wordArithmeticRoof q := mul_word_fee_le hq _ _
  have ae : ad.steps ≤ wordArithmeticRoof q := add_word_fee_le hq _ _
  change O.steps+F.steps+X.steps+S.steps+B.steps+s.steps+c₁.steps+w.steps+c₂.steps+ad.steps+11 ≤ _
  unfold commonLossWordRoof
  omega

#print axioms literal_common_loss_word_exact
#print axioms literal_common_loss_word_fee
#print axioms actual_height_word_exact
#print axioms actual_height_word_fee
end J6R68ActiveInputs
