import J6R36ChildFramedRouteBatch

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13500000

/-! A retained vertex consumes its structured left endpoints. Its
new wire requests are produced by scanning and copying actual rows;
they are not a separately supplied ancestry mapping. -/
namespace J6R36ChildFramedRoute
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R27OriginalGate J6R34ChildPath

def requestView {w key prec page : ℕ} (x : Lane w key prec page) : WireRequest w :=
  ⟨x.id.edge,x.body⟩

def copyRequest {w key prec page : ℕ} (x : Lane w key prec page) : Meter (WireRequest w) :=
  let i := copyFixed x.id.edge
  let body := copyBytes x.body
  ⟨⟨i.result,body.result⟩,i.steps+body.steps+6⟩

def wireFee (w body : ℕ) := 3*w+3*body+8

theorem copy_request_exact {w key prec page : ℕ} (l : Lane w key prec page) :
    copyRequest l=⟨requestView l,wireFee w l.body.length⟩ := by
  simp only [copyRequest,copy_fixed_exact,copyBytes_exact,requestView,wireFee]
  congr 1
  dsimp only
  omega

def collectRetained {w owner key prec page : ℕ} (target : Word owner) :
    List (FramedEdge w owner key prec page)→Meter (List (WireRequest w))
  | [] => ⟨[],3⟩
  | r::rs =>
    let test := cmpAddr target r.oldOwner
    let tail := collectRetained target rs
    if test.result then
      let q := copyRequest r.left
      ⟨q.result::tail.result,test.steps+q.steps+tail.steps+6⟩
    else ⟨tail.result,test.steps+tail.steps+6⟩

def retainVisitFee {w owner key prec page : ℕ} (target : Word owner)
    (r : FramedEdge w owner key prec page) :=
  10*owner+11+(if (cmpAddr target r.oldOwner).result then wireFee w r.left.body.length else 0)

theorem collect_retained_exact {w owner key prec page : ℕ} (target : Word owner)
    (frames : List (FramedEdge w owner key prec page)) :
    let op := collectRetained target frames
    op.result=(frames.filter (fun row=>decide (target=row.oldOwner))).map
        (fun row=>requestView row.left) ∧
      op.steps=3+(frames.map (retainVisitFee target)).sum := by
  induction frames with
  | nil => exact ⟨rfl,rfl⟩
  | cons r rs ih =>
    obtain ⟨read,fee⟩ := ih
    have cmpFee : (cmpAddr target r.oldOwner).steps=10*owner+5 :=
      (cmpAddr_exact _ _).2
    by_cases same : target=r.oldOwner
    · have ok : (cmpAddr target r.oldOwner).result=true := (cmpAddr_exact _ _).1.mpr same
      simp only [collectRetained,ok,if_true,copy_request_exact,cmpFee,read,fee,
        List.filter_cons,decide_eq_true same,List.map_cons,List.sum_cons,retainVisitFee]
      exact ⟨True.intro,by omega⟩
    · have no : (cmpAddr target r.oldOwner).result=false :=
        Bool.eq_false_iff.mpr (fun e=>same ((cmpAddr_exact _ _).1.mp e))
      simp only [collectRetained,no,Bool.false_eq_true,if_false,cmpFee,read,fee,
        List.filter_cons,decide_eq_false same,List.map_cons,List.sum_cons,retainVisitFee]
      exact ⟨True.intro,by omega⟩

theorem structured_requests_for_subtype {E : Type*} {w owner key prec page : ℕ}
    (target : Word owner) (xs : List E) (F : E→FramedEdge w owner key prec page)
    (keep : E→Prop) [DecidablePred keep]
    (correct : ∀ x,target=(F x).oldOwner ↔ keep x) :
    (collectRetained target (xs.map F)).result=
      (scanSubtype keep xs).map (fun x=>requestView (F x.val).left) := by
  rw [(collect_retained_exact target (xs.map F)).1]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : keep x
    · have ok := (correct x).mpr h
      simp only [List.map_cons,List.filter_cons,decide_eq_true ok,if_true,scanSubtype,
        List.filterMap_cons,dif_pos h] at *
      rw [ih]
    · have no : target≠(F x).oldOwner := fun e=>h ((correct x).mp e)
      simp only [List.map_cons,List.filter_cons,decide_eq_false no,Bool.false_eq_true,if_false,
        scanSubtype,List.filterMap_cons,dif_neg h] at *
      exact ih

def retainedInput {w owner a key prec page : ℕ}
    (group : Word 6) (raw : List (PortRow w)) (bank : List (RefRow w (Addon owner a key prec page)))
    (id : Word key) (recv : Word prec) (target : Word owner) : Meter (Option (List (WireRequest w))) :=
  let frames := selectedFrame group raw bank id recv
  match frames.result with
  | none=>⟨none,frames.steps+3⟩
  | some rows=>
    let op := collectRetained target rows
    ⟨some op.result,frames.steps+op.steps+4⟩

#print axioms copy_request_exact
#print axioms collect_retained_exact
#print axioms structured_requests_for_subtype
end J6R36ChildFramedRoute
