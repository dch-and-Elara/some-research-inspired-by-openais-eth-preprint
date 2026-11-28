import J6R63ActivePrefix
import J6R63ActiveControl
import J6R52CacheSourceReplay

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 14000000
set_option maxRecDepth 2600
set_option Elab.async false

/-! The two actual pre-dispatch words for R62. Both come from the
current site: the existing incoming literal header, and the retained
output of the same selected packing. No address to any child of
the current call is an input. -/
namespace J6R63Active
open scoped Polynomial
open Polynomial AOracleMachineTime J6R52CacheSource J6R52FreshExterior
open J6R15ModeCost J6R17ModeTape J6R62ActivePrep
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R33StatefulArithmeticPage
open J6R50SourceProducer

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q q₀ : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) v.child}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) v.child}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "aAt" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s)
  (J6ActiveRun.Call.depth (J6R26DescriptorTree.Ticket.child v)))
local notation "uAt" => (J6ActiveRun.Shape.levelWidth (printedParams (f:=f) (ell:=ell) s)
  (J6ActiveRun.Call.depth (J6R26DescriptorTree.Ticket.child v)))
local notation "pAt" => (registerPrecision S (J6R26DescriptorTree.Ticket.child v) t)

def readInherited (B : Birth T v key prec tw bw page) (raw : List Bool)
    (auth : raw=B.job.entry.result.bytes) :
    Meter (ModeWord prec×ModeWord B.edge) :=
  unwrapSuccess (fromResidentBirth B raw) (by
    rw [(actual_birth_header_words B raw auth).1]
    rfl)

theorem read_inherited_exact (B : Birth T v key prec tw bw page) (raw : List Bool)
    (auth : raw=B.job.entry.result.bytes) :
    readInherited B raw auth=
      ⟨(word v.child.prec,word v.child.edges),callReadFee prec B.edge B.dep B.job.offset⟩ := by
  have H := (actual_birth_header_words B raw auth).1
  unfold readInherited
  rw [unwrap_success_exact _ _ _ (congrArg Meter.result H)]
  exact congrArg (Meter.mk _) (congrArg Meter.steps H)

def precisionFromCurrent (B : Birth T v key prec tw bw page) (raw : List Bool)
    (auth : raw=B.job.entry.result.bytes) (hq : 0<q) (d : Ready S (sourceDelta s) v.child)
    (t : Center S v.child) : Meter (ModeWord q) :=
  let h := readInherited B raw auth
  let p := retainAtWidth q h.result.1
  let m := retainAtWidth q h.result.2
  let u := taperRegister q uAt
  let P := precisionProgram hq aAt (centerIndex d t).val p.result m.result u.result
  ⟨P.result,h.steps+p.steps+m.steps+u.steps+P.steps+5⟩

def currentPrecisionFee (prec edge dep offset q a u : ℕ) : ℕ :=
  callReadFee prec edge dep offset+(2*prec+4*q+5)+(2*edge+4*q+5)+
    taperFee q u+precisionFee a q+5

theorem precision_from_current_exact (B : Birth T v key prec tw bw page)
    (raw : List Bool) (auth : raw=B.job.entry.result.bytes)
    (hq : 0<q) (live : 0<uAt) (width : uAt≤v.child.edges)
    (fit : pAt<2^q) :
    let z := precisionFromCurrent B raw auth hq d t
    z.result.val=pAt ∧
      z.steps≤currentPrecisionFee prec B.edge B.dep B.job.offset q aAt uAt := by
  obtain ⟨baseFit,edgeFit,taperFit,numFit⟩ := header_words_fit_when_receiver_fits d t width fit
  obtain ⟨_,base,edges⟩ := actual_birth_header_words B raw auth
  let P := retainAtWidth q (word (q:=prec) v.child.prec)
  let E := retainAtWidth q (word (q:=B.edge) v.child.edges)
  let U := taperRegister q uAt
  obtain ⟨pVal,pSteps⟩ := retain_at_width_exact q (word (q:=prec) v.child.prec)
    (by rw [base]; exact baseFit)
  obtain ⟨eVal,eSteps⟩ := retain_at_width_exact q (word (q:=B.edge) v.child.edges)
    (by rw [edges]; exact edgeFit)
  have PVal : P.result.val=v.child.prec := pVal.trans base
  have EVal : E.result.val=v.child.edges := eVal.trans edges
  have UVal : U.result.val=uAt := taper_register_value taperFit
  have UCost : U.steps≤taperFee q uAt := taper_register_budget hq _
  let V := precisionProgram hq aAt (centerIndex d t).val P.result E.result U.result
  have VVal : V.result.val=pAt := by
    have one := precision_program_exact hq aAt (centerIndex d t).val P.result E.result U.result
      (UVal.symm ▸ live) (by rw [EVal,UVal]; exact numFit)
      (by rw [PVal,EVal,UVal,printed_precision_at_same_centre d t]; exact fit)
    exact one.trans (by rw [PVal,EVal,UVal,printed_precision_at_same_centre d t])
  have VCost : V.steps≤precisionFee aAt q := precision_program_budget hq _ _ _ _ _
  dsimp only [precisionFromCurrent]
  rw [read_inherited_exact]
  refine ⟨VVal,?_⟩
  change callReadFee prec B.edge B.dep B.job.offset+P.steps+E.steps+U.steps+V.steps+5≤_
  change P.steps=_ at pSteps
  change E.steps=_ at eSteps
  unfold currentPrecisionFee
  omega

def wordsFromCurrent (X : StoredSite T v key prec tw bw page) (raw : List Bool)
    (auth : raw=X.birth.job.entry.result.bytes)
    (hq : 0<q) (live : 0<uAt) (width : uAt≤v.child.edges) (fit : pAt<2^q)
    (L : LayoutReceipt aAt (packing sel d).copies q₀ v.child.edges)
    (copyFits : (packing sel d).copies<2^q) : Meter (CentreWords sel d t q) :=
  let c := copyOfLayout q L
  let p := precisionFromCurrent X.birth raw auth hq d t
  ⟨⟨c.result,p.result,(retained_layout_copy_word L copyFits).1,
    (precision_from_current_exact (d:=d) (t:=t) X.birth raw auth hq live width fit).1⟩,
    c.steps+p.steps+4⟩

theorem actual_two_words_form_paid_tape
    (X : StoredSite T v key prec tw bw page) (raw : List Bool)
    (auth : raw=X.birth.job.entry.result.bytes)
    (hq : 0<q) (live : 0<uAt) (width : uAt≤v.child.edges) (fit : pAt<2^q)
    (L : LayoutReceipt aAt (packing sel d).copies q₀ v.child.edges)
    (copyFits : (packing sel d).copies<2^q) (axisFits : (centerIndex d t).val+1<q) :
    let input := wordsFromCurrent X raw auth hq live width fit L copyFits
    let tape := paidTape hq axisFits input
    input.result.copies.val=(packing sel d).copies ∧ input.result.precision.val=pAt ∧
    tape.steps≤2*q₀+4*q+9+
      currentPrecisionFee prec X.birth.edge X.birth.dep X.birth.job.offset q aAt uAt+
      canonicalCap aAt q (centerIndex d t).val (packing sel d).copies pAt := by
  let input := wordsFromCurrent X raw auth hq live width fit L copyFits
  have prep := (precision_from_current_exact (d:=d) (t:=t) X.birth raw auth hq live width fit).2
  have copied := (retained_layout_copy_word L copyFits).2
  have old := (paid_tape_local_fee hq axisFits input).2
  refine ⟨input.result.copiesExact,input.result.precisionExact,old.trans ?_⟩
  change (copyOfLayout q L).steps+(precisionFromCurrent X.birth raw auth hq d t).steps+4+
    canonicalCap aAt q (centerIndex d t).val (packing sel d).copies pAt≤_
  omega

#print axioms read_inherited_exact
#print axioms precision_from_current_exact
#print axioms actual_two_words_form_paid_tape
end
end J6R63Active

