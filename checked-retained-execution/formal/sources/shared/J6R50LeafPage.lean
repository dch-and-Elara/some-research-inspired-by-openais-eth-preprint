import J6R34ChildPathWires
import J6R36ChildFramedRouteCarry
import J6R49LeafOriginal

/-! For a native/exterior retained row, buy its owner-key scan, ancestor
stamp, page key, explicit depth clock and all raw edge-address seeks.
The input is shared resident incidence and an existing owner record,
not a list of ready-to-read ordinal lanes. -/
namespace J6R50Leaf
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R34ChildPath J6R36ChildFramedRoute J6R33StatefulArithmeticPage
open J6R25PreparedSupply J6R26DescriptorTree J6R20Ancestor J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000

def depthClock : List Bool → Meter ℕ
  | [] => ⟨0,2⟩
  | _::rest =>
    let prev := depthClock rest
    ⟨prev.result+1,prev.steps+4⟩

theorem depth_clock_exact (ticks : List Bool) :
    depthClock ticks=⟨ticks.length,4*ticks.length+2⟩ := by
  induction ticks with
  | nil => rfl
  | cons h hs ih =>
    simp only [depthClock,ih,List.length_cons]
    congr 1

abbrev ResidentPort (own w : ℕ) := RefRow own (WireRequest w)

def copyIncoming {w : ℕ} (line : WireRequest w) : Meter (WireRequest w) :=
  let w := copyFixed line.incumbent
  let h := copyBytes line.ancestry
  ⟨⟨w.result,h.result⟩,w.steps+h.steps+6⟩

theorem copy_incoming_exact {w : ℕ} (line : WireRequest w) :
    copyIncoming line=⟨line,3*w+3*line.ancestry.length+8⟩ := by
  cases line
  simp only [copyIncoming,copy_fixed_exact,copyBytes_exact]
  congr 1
  omega

def incomingVisitFee {own w : ℕ} (owner : Word own) (line : ResidentPort own w) :=
  10*own+11+(if (cmpAddr owner line.address).result then 3*w+3*line.payload.ancestry.length+8 else 0)

def collectIncoming {own w : ℕ} (owner : Word own) :
    List (ResidentPort own w) → Meter (List (WireRequest w))
  | [] => ⟨[],3⟩
  | r::rs =>
    let seen := cmpAddr owner r.address
    let tail := collectIncoming owner rs
    if seen.result then
      let row := copyIncoming r.payload
      ⟨row.result::tail.result,seen.steps+tail.steps+row.steps+6⟩
    else ⟨tail.result,seen.steps+tail.steps+6⟩

theorem collect_incoming_exact {own w : ℕ} (owner : Word own)
    (lines : List (ResidentPort own w)) :
    let op := collectIncoming owner lines
    op.result=(lines.filter (fun r=>(cmpAddr owner r.address).result)).map RefRow.payload ∧
      op.steps=3+(lines.map (incomingVisitFee owner)).sum := by
  induction lines with
  | nil => exact ⟨rfl,rfl⟩
  | cons r rs ih =>
    obtain ⟨hr,fee⟩ := ih
    have cFee := (cmpAddr_exact owner r.address).2
    by_cases eq : owner=r.address
    · have ok := (cmpAddr_exact owner r.address).1.mpr eq
      simp only [collectIncoming,ok,if_true,copy_incoming_exact,cFee,hr,fee,
        List.filter_cons,List.map_cons,List.sum_cons,incomingVisitFee]
      exact ⟨True.intro,by omega⟩
    · have no : (cmpAddr owner r.address).result=false :=
        Bool.eq_false_iff.mpr (fun h=>eq ((cmpAddr_exact _ _).1.mp h))
      simp only [collectIncoming,no,Bool.false_eq_true,if_false,cFee,hr,fee,
        List.filter_cons,List.map_cons,List.sum_cons,incomingVisitFee]
      exact ⟨True.intro,by omega⟩

structure PageOrigin (key prec page : ℕ) where
  header : Origin key prec page
  clock : List Bool

def buildPage {own w key prec page : ℕ} (M : ℕ) (keys : List (Word w))
    (owner : Word own) (lines : List (ResidentPort own w)) (site : PageOrigin key prec page) :
    Meter (Option (PageReadCode M key page)) :=
  let head := copyOrigin site.header
  let d := depthClock site.clock
  match head.result.pageKey with
  | none => ⟨none,head.steps+d.steps+5⟩
  | some pageID =>
    let incoming := collectIncoming owner lines
    let shifted := emitWires keys incoming.result
    ⟨shifted.result.map (.generated head.result.stamp.creator pageID d.result),
      head.steps+d.steps+incoming.steps+shifted.steps+8⟩

def pageBuildFee {own w : ℕ} (owner : Word own) (lines : List (ResidentPort own w))
    (key prec page ticks wireFee : ℕ) : ℕ :=
  originFee key prec page true+(4*ticks+2)+(3+(lines.map (incomingVisitFee owner)).sum)+
    (4+wireFee)+8

theorem build_page_from_resident {V : Type*} {N own w key prec page : ℕ}
    (keys : List (Word w)) (keyAt : Fin N→Word w)
    (inj : Function.Injective keyAt) (realKeys : keys=List.ofFn keyAt)
    (owner : Word own) (lines : List (ResidentPort own w))
    (site : PageOrigin key prec page) (born : Stamp key prec) (pageKey : Word page)
    (isSite : site.header=⟨born,some pageKey⟩)
    (ports : List V) (header : V→List Bool) (ordinal : V→Fin N)
    (realPorts : (lines.filter (fun r=>(cmpAddr owner r.address).result)).map RefRow.payload =
      ports.map (fun u=>⟨keyAt (ordinal u),header u⟩)) :
    let run := buildPage N keys owner lines site
    run.result=some (.generated born.creator pageKey site.clock.length
      (ports.map (fun u=>⟨header u,List.replicate (ordinal u).val true⟩))) ∧
      run.steps=pageBuildFee owner lines key prec page site.clock.length
        (ports.map (fun u=>sourceWireFee w (ordinal u).val (header u).length)).sum := by
  obtain ⟨found,bill⟩ := collect_incoming_exact owner lines
  obtain ⟨emit,cost⟩ := source_wire_tape keys keyAt inj realKeys ports header ordinal
    (collectIncoming owner lines).result (found.trans realPorts)
  dsimp only at emit cost bill ⊢
  unfold buildPage
  rw [isSite,copy_origin_exact,depth_clock_exact]
  dsimp only
  rw [emit,cost,bill]
  exact ⟨rfl,rfl⟩

#print axioms depth_clock_exact
#print axioms collect_incoming_exact
#print axioms build_page_from_resident
end J6R50Leaf
