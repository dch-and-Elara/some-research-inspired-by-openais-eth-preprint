import J6R51LeafCore
import J6R41StructuredAllPathsLocal
import J6R50LeafLineage

/-! A fresh native Page has no predecessor route. Its leaf input words
are emitted by scanning the *same* right-hand fields of the real
selected frame, matching its literal Page key. No desired wire list is
a runtime input to this scan. -/
namespace J6R51Leaf
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R15ModeCost 
open J6R41StructuredAllPaths J6R36ChildFramedRoute J6R34ChildPath J6R50Leaf
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R26DescriptorTree J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R50SourceProducer
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000
set_option maxRecDepth 3400

def chooseFresh {w own key prec page : ℕ} (k : Word page)
    (v : FramedEdge w own key prec page) : Option (WireRequest w) :=
  match v.right.origin.pageKey with
  | none => none
  | some id=>if (cmpAddr k id).result then some (requestView v.right) else none

def freshVisitFee {w own key prec page : ℕ} (k : Word page)
    (v : FramedEdge w own key prec page) : ℕ :=
  match v.right.origin.pageKey with
  | none => 4
  | some id => 10*page+11+
    (if (cmpAddr k id).result then 3*w+3*v.right.body.length+8 else 0)

def scanFresh {w own key prec page : ℕ} (k : Word page) :
    List (FramedEdge w own key prec page)→Meter (List (WireRequest w))
  | [] => ⟨[],3⟩
  | v::vs =>
    let r := scanFresh k vs
    match v.right.origin.pageKey with
    | none=>⟨r.result,r.steps+4⟩
    | some id=>
      let cmp := cmpAddr k id
      if cmp.result then
        let fresh := copyIncoming (requestView v.right)
        ⟨fresh.result::r.result,cmp.steps+r.steps+fresh.steps+6⟩
      else ⟨r.result,cmp.steps+r.steps+6⟩

theorem scan_fresh_exact {w own key prec page : ℕ} (k : Word page)
    (frames : List (FramedEdge w own key prec page)) :
    scanFresh k frames=⟨frames.filterMap (chooseFresh k),
      3+(frames.map (freshVisitFee k)).sum⟩ := by
  induction frames with
  | nil => rfl
  | cons v vs ih =>
    simp only [scanFresh,ih,List.filterMap_cons,List.map_cons,List.sum_cons]
    cases old : v.right.origin.pageKey with
    | none =>
      simp only [old,chooseFresh,freshVisitFee]
      congr 1
      omega
    | some id =>
      have n := (cmpAddr_exact k id).2
      cases h : (cmpAddr k id).result
      · simp only [old,n,h,Bool.false_eq_true,if_false,chooseFresh,freshVisitFee]
        congr 1
        omega
      · simp only [old,n,h,if_true,chooseFresh,freshVisitFee,copy_incoming_exact,requestView]
        congr 1
        omega

def runFreshFrames {w own key prec page : ℕ} (setup : ℕ)
    (phase : Meter (FramedIssue key w own prec page)) (id : Word page) :
    Meter (Option (List (WireRequest w))) :=
  match phase.result.framed with
  | none => ⟨none,setup+phase.steps+3⟩
  | some frames =>
    let r := scanFresh id frames
    ⟨some r.result,setup+phase.steps+r.steps+5⟩

theorem run_fresh_frames_exact {w own key prec page : ℕ} (setup : ℕ)
    (phase : Meter (FramedIssue key w own prec page)) (id : Word page)
    (frames : List (FramedEdge w own key prec page)) (has : phase.result.framed=some frames) :
    runFreshFrames setup phase id=
      ⟨some (frames.filterMap (chooseFresh id)),
        setup+phase.steps+3+(frames.map (freshVisitFee id)).sum+5⟩ := by
  unfold runFreshFrames
  rw [has]
  dsimp only
  rw [scan_fresh_exact]
  simp only [Nat.add_assoc]

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (site : StoredSite T v key prec tw bw page)

def paidFreshRequests (id : Word page) :
    Meter (Option (List (WireRequest site.birth.port))) :=
  runFreshFrames site.site.install.steps site.site.write id

theorem fresh_requests_from_same_issued_frames (id : Word page) :
    let frames := (halfOrder T v site.birth.native.physical).map site.site.frame
    paidFreshRequests site id=
      ⟨some (frames.filterMap (chooseFresh id)),
        site.site.install.steps+site.site.write.steps+3+
          (frames.map (freshVisitFee id)).sum+5⟩ :=
  run_fresh_frames_exact site.site.install.steps site.site.write id _ (true_site_issuance site.site).2.2.2

#print axioms scan_fresh_exact
#print axioms fresh_requests_from_same_issued_frames
end
end J6R51Leaf
