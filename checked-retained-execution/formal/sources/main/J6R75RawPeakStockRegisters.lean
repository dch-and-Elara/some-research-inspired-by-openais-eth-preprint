import J6R68ActiveInputsBaseCurrent

/-! Actual fixed-width register outputs of the entered leafless
stock height and common-margin producers. The bit tally names
their captured intermediate words, not internal divider/multiplier
gate temporaries or an execution stack. -/
namespace J6R75RawPeak
open AOracleMachineTime A1R10 J6R68ActiveInputs
open J6R22RootReadout J6R52FreshExterior

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3100
set_option maxHeartbeats 6200000
set_option Elab.async false

def qBankWords {q : ℕ} (words : List (Word q)) : ℕ :=
  (words.map (fun w=>w.val.length)).sum

theorem q_bank_words_exact {q : ℕ} (words : List (Word q)) :
    qBankWords words=q*words.length := by
  induction words with
  | nil=>simp [qBankWords]
  | cons z zs ih=>
    change z.val.length+qBankWords zs=q*(zs.length+1)
    rw [z.property,ih,Nat.mul_succ,Nat.add_comm]

def stockHeightFields {q : ℕ} (hq : 0<q) (edge taper : J6R15ModeCost.Word q) :
    List (Word q)×Meter (Word q) :=
  let E := modeWordAsA edge
  let U := modeWordAsA taper
  let o := constantRegister q [true]
  let t := constantRegister q [true,true]
  let extra := subWord hq U o.result
  let triple := mulWord t.result E
  let sum := addWord triple.result extra.result
  let div := divideMagnitude sum.result U
  ([E,U,o.result,t.result,extra.result,triple.result,sum.result,div.result],
    ⟨div.result,o.steps+t.steps+extra.steps+triple.steps+sum.steps+div.steps+8⟩)

theorem actual_stock_height_has_the_selected_fixed_words {q : ℕ}
    (hq : 0<q) (edge taper : J6R15ModeCost.Word q) :
    heightWord hq edge taper=(stockHeightFields hq edge taper).2 ∧
    qBankWords (stockHeightFields hq edge taper).1=8*q := by
  refine ⟨rfl,?_⟩
  rw [q_bank_words_exact]
  change q*8=8*q
  exact Nat.mul_comm _ _

def stockMarginFields {q : ℕ} (a : ℕ) (edge h : Word q) :
    List (Word q)×Meter (Word q) :=
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
  ([edge,h,one.result,four.result,six.result,scale.result,slope.result,
    s.result,c₁.result,w.result,c₂.result,out.result],
    ⟨out.result,one.steps+four.steps+six.steps+scale.steps+slope.steps+
      s.steps+c₁.steps+w.steps+c₂.steps+out.steps+11⟩)

theorem actual_stock_margin_has_the_selected_fixed_words {q : ℕ}
    (a : ℕ) (edge h : Word q) :
    commonLossWord a edge h=(stockMarginFields a edge h).2 ∧
    qBankWords (stockMarginFields a edge h).1=12*q := by
  refine ⟨rfl,?_⟩
  rw [q_bank_words_exact]
  change q*12=12*q
  exact Nat.mul_comm _ _

#print axioms q_bank_words_exact
#print axioms actual_stock_height_has_the_selected_fixed_words
#print axioms actual_stock_margin_has_the_selected_fixed_words
end J6R75RawPeak
