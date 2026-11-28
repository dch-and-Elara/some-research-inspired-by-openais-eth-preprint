import J6R68ActiveInputsBaseRoster
import J6R68ActiveInputsBaseFits

/-! The current node's captured edge word and taper produce the
entire stock table and high margin with a single restoring-divide
height computation. This module accepts the captured header value
rather than reading a second header or touching a future address. -/
namespace J6R68ActiveInputs
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 J6R22RootReadout J6R52FreshExterior J6R22Active
open J6ActiveSchedule J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R63Active J6R64Active J6R15ModeCost

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000
set_option maxRecDepth 3500
set_option maxSynthPendingDepth 12
set_option Elab.async false

structure RawBaseStock (q : ℕ) where
  rows : List (RawCentre q)
  margin : A1R10.Word q

def paidStockAndMargin {q : ℕ} (hq : 0<q) (a u : ℕ) (edge taper : J6R15ModeCost.Word q) :
    Meter (RawBaseStock q) :=
  let A := ticks a
  let U := ticks u
  let G := signedGridTape a
  let H := heightWord hq edge taper
  let z := constantRegister q []
  let d := scanOrders z.result H.result A.result U.result G.result
  let margin := commonLossWord a (modeWordAsA edge) H.result
  ⟨⟨d.result,margin.result⟩,A.steps+U.steps+G.steps+H.steps+z.steps+d.steps+8+margin.steps+4⟩

theorem stock_reuses_a_single_height_register {q : ℕ} (hq : 0<q) (a u : ℕ)
    (edge taper : J6R15ModeCost.Word q) :
    let S := paidStockAndMargin hq a u edge taper
    let D := paidBaseTape hq a u edge taper
    let l := commonLossWord a (modeWordAsA edge) (heightWord hq edge taper).result
    S.result.rows=D.result ∧ S.result.margin=l.result ∧ S.steps=D.steps+l.steps+4 :=
  ⟨rfl,rfl,rfl⟩

theorem true_stock_and_common_margin_are_measured {q a M u : ℕ} (hq : 0<q)
    (edge taper : J6R15ModeCost.Word q) (e : edge.val=M) (v : taper.val=u)
    (hu : 0<u) (hm : u ≤ M) (num : 3*M+u-1<2^q) (orders : 4*M<2^q)
    (fits : commonLoss a M u<2^q) :
    let B := paidStockAndMargin hq a u edge taper
    StockTapeCorrect a M u B.result.rows ∧
      bitsValue B.result.margin.val=commonLoss a M u ∧
      B.steps ≤ baseTapeRoof a u q+commonLossWordRoof a q+4 := by
  let S := paidStockAndMargin hq a u edge taper
  let F := paidBaseTape hq a u edge taper
  let H := heightWord hq edge taper
  let m := commonLossWord a (modeWordAsA edge) H.result
  have eS := stock_reuses_a_single_height_register hq a u edge taper
  have h : bitsValue H.result.val=height M u := by
    have G := actual_height_word_exact hq edge taper (v.symm ▸ hu) (e.symm ▸ v.symm ▸ num)
    rwa [e,v] at G
  refine ⟨?_,?_,?_⟩
  · change StockTapeCorrect a M u S.result.rows
    rw [show S.result.rows=F.result from eS.1]
    exact paid_base_has_roster_receipt hq edge taper e v hu hm num orders
  · change bitsValue m.result.val=commonLoss a M u
    exact literal_common_loss_word_exact (modeWordAsA edge) H.result e h fits
  · change S.steps ≤ _
    rw [eS.2.2]
    have h₁ := (actual_base_tape_has_stock_census (a:=a) hq edge taper e v hu hm num orders).2.2.2
    have h₂ := literal_common_loss_word_fee hq a (modeWordAsA edge) H.result
    exact Nat.add_le_add_right (Nat.add_le_add h₁ h₂) 4

noncomputable section
variable {f : ℤ[X]} {ell s q pw ew : ℕ} {c : Call (PhysicalHost f ell)}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
local notation "A" => (Shape.levelBits (printedParams (f:=f) (ell:=ell) s) c.depth)
local notation "U" => (Shape.levelWidth (printedParams (f:=f) (ell:=ell) s) c.depth)

def prepareStockFromHeader (hq : 0<q) (W : CallWords c pw ew) :
    Meter (RawBaseStock q) :=
  let m := retainAtWidth q W.edges
  let u := taperRegister q U
  let S := paidStockAndMargin hq A U m.result u.result
  ⟨S.result,m.steps+u.steps+S.steps+6⟩

theorem actual_current_word_builds_stock_and_margin (hq : 0<q) (W : CallWords c pw ew)
    (fit : InputFits sel d q) (taperPos : 0<U) (taperSmall : U ≤ c.edges) :
    let B := prepareStockFromHeader (s:=s) hq W
    StockTapeCorrect A c.edges U B.result.rows ∧
      bitsValue B.result.margin.val=commonLoss A c.edges U ∧
      B.steps ≤ (2*ew+4*q+5)+taperFee q U+
        (baseTapeRoof A U q+commonLossWordRoof A q+4)+6 := by
  obtain ⟨num,orders,margin,edges,u⟩ := true_native_registers_fit_base_operations fit taperPos taperSmall
  let m := retainAtWidth q W.edges
  let t := taperRegister q U
  obtain ⟨me,mf⟩ := retain_at_width_exact q W.edges (W.edgesValue.symm ▸ edges)
  have e : m.result.val=c.edges := me.trans W.edgesValue
  have v : t.result.val=U := taper_register_value u
  have recorded := true_stock_and_common_margin_are_measured (a:=A) hq m.result t.result e v taperPos
    taperSmall num orders margin
  have bill := taper_register_budget hq U
  exact ⟨recorded.1,recorded.2.1,Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add mf.le bill) recorded.2.2) 6⟩
end

#print axioms stock_reuses_a_single_height_register
#print axioms true_stock_and_common_margin_are_measured
#print axioms actual_current_word_builds_stock_and_margin
end J6R68ActiveInputs
