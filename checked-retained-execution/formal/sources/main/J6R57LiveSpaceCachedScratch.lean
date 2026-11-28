import J6R57LiveSpaceCachedMode
import J6R57LiveSpaceMulScratch
import J6R50PeakStartPrecision

/-! A current arithmetic scratch cut: the selected cached child has
returned its genuine word and the pending group product starts its V
convolution. Count that returned word and the five arrays of one
actual convolution unwind. Do not put this scratch in every ancestor. -/
namespace J6R57LiveSpace
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active J6R21Leaf
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R17ModeTape J6R24MeteredRecursion J6R25PreparedSupply
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS J6R49LiveBits
open J6R51Online J6R52Peak J6R53PeakAddon J6R50Peak
set_option autoImplicit false
set_option maxRecDepth 4250
set_option maxHeartbeats 27000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "Bnk" => PageBank f ell key prec tw bw page
local notation "Job" => PageJob f ell key prec tw bw page

theorem same_cached_group_resume_bounds_one_current_scratch
    (M : OnlineMachine T key prec tw bw page q) (retire : Job→ℕ) (initial : Bnk)
    (fits : q≤uniformWidth s C) (p : Path sel r c) (w : (P).Slot c) :
    let d := ready_reachable cfg sel p.reached T.rootStable w.property
    let t := w.val.1
    let z := w.val.2.1
    let β := w.val.2.2.1
    let g := w.val.2.2.2
    let F := T.bank (registerPrecision S c t) (register_positive d t)
    let I := ((activeAt M p w.property).result.tape t).tape.result
    let read := cachedReadAt M retire initial p w.property t z
    ∃ (o : NativeSuspension (C:=C) (sel:=sel) c) (now : Pending q I.words.length)
      (outer inner : Block F ell) (fee feeM : ℕ)
      (raw : List (J6R15ModeCost.Word q)) (next : J6R15ModeCost.State q) (left : List (Fin 64)),
      SawCachedMode M retire initial p w o ∧
      GroupPrefix F.hp (read β) (oneM F.hp F.sizePos T.vPositive).result
        (oneM F.hp F.sizePos T.vPositive).steps (g::left) inner feeM ∧
      ∃ emit : now.pulse.result=.emit raw next,
      (let mul := mulM F.hp ⟨inner,0⟩ (read β g)
       let prod := productCursor F.hp (read β) left mul.result (feeM+mul.steps)
       let sum := addM F.hp ⟨outer,0⟩ prod
       let tail := modeDrain (modeUpdate F I T.vPositive read) (now.tail emit) sum.result
         (fee+now.pulse.steps+sum.steps)
       runProbe F I M.modeWidth T.vPositive read=⟨tail.result.1,tail.steps⟩) ∧
      ∀ pre x xs, inner.val=pre++(x::xs) →
        (leafPayload (read β g).result).length+selectedVScratch F x xs (read β g).result≤
          (11*ell)*(f.natDegree*absolutePrecision s r.edges r.prec) := by
  let a := w.property
  let d := ready_reachable cfg sel p.reached T.rootStable a
  let t := w.val.1
  let z := w.val.2.1
  let β := w.val.2.2.1
  let g := w.val.2.2.2
  let F := T.bank (registerPrecision S c t) (register_positive d t)
  let read := cachedReadAt M retire initial p a t z
  obtain ⟨o,history⟩ := each_cached_slot_has_its_real_mode_event M retire initial fits p w
  have records := history
  dsimp only [SawCachedMode] at records
  obtain ⟨_,started,now,outer,inner,fee,feeM,raw,next,left,start,proceeded,emit,decoded,group,view,resume⟩ := records
  refine ⟨o,now,outer,inner,fee,feeM,raw,next,left,history,group,emit,resume,?_⟩
  intro pre x xs segment
  have AR := (actual_mulM_retains_its_true_five_suffix_arrays F hf inner (read β g) pre x xs segment).2.2
  have output := leaf_payload_width (read β g).result
  rw [F.natDegree hf] at output
  change (leafPayload (read β g).result).length+selectedVScratch F x xs (read β g).result≤_
  have lo := absolute_register_precision_cap cfg sel T.rootStable p a t
  calc
    _ ≤ ell*(f.natDegree*registerPrecision S c t)+(10*ell)*(f.natDegree*registerPrecision S c t) :=
          Nat.add_le_add output.le AR
    _ = (11*ell)*(f.natDegree*registerPrecision S c t) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ lo)

#print axioms same_cached_group_resume_bounds_one_current_scratch
end
end J6R57LiveSpace
