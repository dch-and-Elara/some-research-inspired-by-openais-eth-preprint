import J6R64ActiveIncoming
import J6R62ActivePrepBudget

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16500000
set_option maxRecDepth 3000
set_option Elab.async false

/-! Once per active call: read its inherited header and retain the
copy-count word from the selected layout. Per centre: compute the
precision from those same shared words, then build its actual R62
coordinate tape and pass it to runCentre. -/
namespace J6R64Active
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape
open J6R63Active J6R62ActivePrep J6R52FreshExterior
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R49DFS J6R32StatefulArithmetic

noncomputable section
variable {f : ℤ[X]} {ell s C q pw ew cw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c} {bank : Bank f}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "aAt" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s)
  (J6ActiveRun.Call.depth c))
local notation "uAt" => (J6ActiveRun.Shape.levelWidth (printedParams (f:=f) (ell:=ell) s)
  (J6ActiveRun.Call.depth c))

abbrev AtLayout (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (d : Ready S (sourceDelta s) c) (cw : ℕ) :=
  LayoutReceipt aAt (packing sel d).copies cw c.edges

structure InputFits (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (d : Ready S (sourceDelta s) c) (q : ℕ) : Prop where
  copies : (packing sel d).copies < 2^q
  axis : ∀ t : Center S c, (centerIndex d t).val+1<q
  register : ∀ t : Center S c, registerPrecision S c t<2^q

def centrePrecision (hq : 0<q) (d : Ready S (sourceDelta s) c)
    (t : Center S c) (W : CallWords c pw ew) : Meter (Word q) :=
  let p := retainAtWidth q W.precision
  let m := retainAtWidth q W.edges
  let u := taperRegister q uAt
  let X := precisionProgram hq aAt (centerIndex d t).val p.result m.result u.result
  ⟨X.result,p.steps+m.steps+u.steps+X.steps+4⟩

def ctrlFee (pw ew q a u : ℕ) : ℕ :=
  (2*pw+4*q+5)+(2*ew+4*q+5)+taperFee q u+precisionFee a q+4

theorem centre_precision_from_shared_words
    (hq : 0<q) (d : Ready S (sourceDelta s) c) (t : Center S c) (W : CallWords c pw ew)
    (taperPos : 0<uAt) (taperSmall : uAt ≤ c.edges) (fit : registerPrecision S c t<2^q) :
    let p := centrePrecision hq d t W
    p.result.val=registerPrecision S c t ∧ p.steps ≤ ctrlFee pw ew q aAt uAt := by
  obtain ⟨baseFit,edgeFit,taperFit,numFit⟩ := header_words_fit_when_receiver_fits d t taperSmall fit
  let P := retainAtWidth q W.precision
  let E := retainAtWidth q W.edges
  let U := taperRegister q uAt
  obtain ⟨pVal,pSteps⟩ := retain_at_width_exact q W.precision (W.precisionValue.symm ▸ baseFit)
  obtain ⟨eVal,eSteps⟩ := retain_at_width_exact q W.edges (W.edgesValue.symm ▸ edgeFit)
  have PVal : P.result.val=c.prec := pVal.trans W.precisionValue
  have EVal : E.result.val=c.edges := eVal.trans W.edgesValue
  have UVal : U.result.val=uAt := taper_register_value taperFit
  have UFee : U.steps ≤ taperFee q uAt := taper_register_budget hq _
  let v := precisionProgram hq aAt (centerIndex d t).val P.result E.result U.result
  have val : v.result.val=registerPrecision S c t := by
    have law := precision_program_exact hq aAt (centerIndex d t).val P.result E.result U.result
      (UVal.symm ▸ taperPos) (by rw [EVal,UVal]; exact numFit)
      (by rw [PVal,EVal,UVal,printed_precision_at_same_centre d t]; exact fit)
    exact law.trans (by rw [PVal,EVal,UVal,printed_precision_at_same_centre d t])
  have fees : v.steps ≤ precisionFee aAt q := precision_program_budget hq _ _ _ _ _
  change P.steps=_ at pSteps
  change E.steps=_ at eSteps
  refine ⟨val,?_⟩
  change P.steps+E.steps+U.steps+v.steps+4 ≤ _
  unfold ctrlFee
  omega

def centreWords (hq : 0<q) (F : InputFits sel d q)
    (taperPos : 0<uAt) (taperSmall : uAt ≤ c.edges) (W : CallWords c pw ew)
    (copies : Word q) (copyLaw : copies.val=(packing sel d).copies) (t : Center S c) :
    Meter (CentreWords sel d t q) :=
  let P := centrePrecision hq d t W
  ⟨⟨copies,P.result,copyLaw,(centre_precision_from_shared_words hq d t W taperPos taperSmall (F.register t)).1⟩,
    P.steps+3⟩

def sharedMachine (hq : 0<q) (F : InputFits sel d q)
    (taperPos : 0<uAt) (taperSmall : uAt ≤ c.edges)
    (W : Meter (CallWords c pw ew)) (L : Meter (AtLayout sel d cw))
    (D : Meter (ActiveMachine sel d bank q)) : Meter (ActiveMachine sel d bank q) :=
  let copy := copyOfLayout q L.result
  let fixed := (retained_layout_copy_word L.result F.copies).1
  let V t := centreWords hq F taperPos taperSmall W.result copy.result fixed t
  ⟨{D.result with tape:=fun t=>mountAtCentre (D.result.tape t) hq (F.axis t) (V t)},
    D.steps+W.steps+L.steps+copy.steps+4⟩

theorem shared_setup_has_one_header_and_one_layout
    (hq : 0<q) (F : InputFits sel d q) (taperPos : 0<uAt) (taperSmall : uAt ≤ c.edges)
    (W : Meter (CallWords c pw ew)) (L : Meter (AtLayout sel d cw))
    (D : Meter (ActiveMachine sel d bank q)) :
    let V := sharedMachine hq F taperPos taperSmall W L D
    V.steps=D.steps+W.steps+L.steps+(2*cw+4*q+5)+4 ∧
      V.result.centres=D.result.centres ∧ V.result.extraPrecision=D.result.extraPrecision ∧
      (∀ t, (V.result.tape t).roster=(D.result.tape t).roster ∧
        (V.result.tape t).masks=(D.result.tape t).masks) := by
  refine ⟨?_,rfl,rfl,fun _=>⟨rfl,rfl⟩⟩
  dsimp only [sharedMachine]
  rw [(retained_layout_copy_word L.result F.copies).2]

theorem actual_centre_tape_uses_shared_words
    (hq : 0<q) (F : InputFits sel d q) (taperPos : 0<uAt) (taperSmall : uAt ≤ c.edges)
    (W : Meter (CallWords c pw ew)) (L : Meter (AtLayout sel d cw))
    (D : Meter (ActiveMachine sel d bank q)) (t : Center S c) :
    ((sharedMachine hq F taperPos taperSmall W L D).result.tape t).tape.steps ≤
      ctrlFee pw ew q aAt uAt+3+
        canonicalCap aAt q (centerIndex d t).val (packing sel d).copies (registerPrecision S c t) := by
  let V := centreWords hq F taperPos taperSmall W.result (copyOfLayout q L.result).result
    (retained_layout_copy_word L.result F.copies).1 t
  have cost := (paid_tape_local_fee hq (F.axis t) V).2
  have P := (centre_precision_from_shared_words hq d t W.result taperPos taperSmall (F.register t)).2
  change (centrePrecision hq d t W.result).steps ≤ _ at P
  exact cost.trans (Nat.add_le_add_right (Nat.add_le_add_right P 3) _)

theorem shared_active_value
    (hq : 0<q) (F : InputFits sel d q) (taperPos : 0<uAt) (taperSmall : uAt ≤ c.edges)
    (W : Meter (CallWords c pw ew)) (L : Meter (AtLayout sel d cw))
    (D : Meter (ActiveMachine sel d bank q))
    (hp : 0<c.prec) (hv : 0<ell) (monic : f.Monic)
    (read : ActiveChild (sel:=sel) (d:=d) bank) :
    let V := (sharedMachine hq F taperPos taperSmall W L D).result
    (V.eval hq hp hv monic read).result=(D.result.eval hq hp hv monic read).result := by
  let V := (sharedMachine hq F taperPos taperSmall W L D).result
  have high : (V.highRun hq hp hv monic read).result=
      (D.result.highRun hq hp hv monic read).result := by
    apply sum_raw_congr
    intro t _
    exact mounted_tape_keeps_typed_centre_value (D.result.tape t) hq (F.axis t) _
      hv monic (D.result.high hp) D.result.extraPrecision (read t)
  have finis : (V.finish hq hp hv monic read).result=(D.result.finish hq hp hv monic read).result := by
    unfold ActiveMachine.finish
    dsimp only
    rw [high]
  change (V.eval hq hp hv monic read).result=(D.result.eval hq hp hv monic read).result
  unfold ActiveMachine.eval checkedWord
  rw [finis]
  cases (D.result.finish hq hp hv monic read).result <;> rfl

theorem actual_path_taper (T : Prepared cfg sel r hf) (p : Path sel r c)
    (active : (S).cutoff<c.edges) : 0<uAt ∧ uAt ≤ c.edges :=
  (J6R12Integral.printedGuards cfg sel r T.rootStable).taper _ p.reached active

#print axioms centre_precision_from_shared_words
#print axioms shared_setup_has_one_header_and_one_layout
#print axioms actual_centre_tape_uses_shared_words
#print axioms shared_active_value
#print axioms actual_path_taper
end
end J6R64Active

