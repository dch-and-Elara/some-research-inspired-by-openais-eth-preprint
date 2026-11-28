import J6R62LeafWirePrep
import J6R52TerminalAncestorFrames
import J6R52TerminalFreshCore
import J6R48LeafRawReader

/-! Length bounds on the *produced* leaf wire arguments. This uses
the genuine scan/copy producer, not a claimed fee for its output.
Byte sizes of the installed parent frame headers remain separate. -/
namespace J6R66LeafTariff
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R34ChildPath J6R36ChildFramedRoute J6R51ParentFrames J6R48Leaf
open J6R52Terminal J6R50Leaf J6R62Leaf J6R51Leaf

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 3200
set_option Elab.async false

theorem true_wire_keeps_the_header_and_fits_the_book {w : ℕ}
    (keys : List (Word w)) (req : WireRequest w) (v : WireRead)
    (emitted : (emitWire keys req).result=some v) :
    v.header=req.ancestry ∧ v.lane.length≤keys.length := by
  cases pos : (seekLane req.incumbent keys).result with
  | none => simp [emitWire,pos] at emitted
  | some lane =>
    have eq : (⟨req.ancestry,lane⟩ : WireRead)=v := by
      simpa only [emitWire,pos,copyBytes_exact,Option.map_some,Option.some.injEq] using emitted
    subst v
    exact ⟨rfl,(seek_lane_bounded req.incumbent keys).2 lane pos⟩

theorem true_wire_tape_lengths {w U : ℕ} (keys : List (Word w))
    (reqs : List (WireRequest w)) (fits : RequestsFit reqs U)
    (rs : List WireRead) (ok : (emitWires keys reqs).result=some rs) :
    rs.length=reqs.length ∧ ∀ v∈rs,v.header.length≤U ∧ v.lane.length≤keys.length := by
  induction reqs generalizing rs with
  | nil =>
    have eq : []=rs := by simpa only [emitWires,Option.some.injEq] using ok
    subst rs
    simp
  | cons h ts ih =>
    cases just : (emitWire keys h).result with
    | none => simp [emitWires,just] at ok
    | some v =>
      cases later : (emitWires keys ts).result with
      | none => simp [emitWires,just,later] at ok
      | some vs =>
        have eq : v::vs=rs := by
          simpa only [emitWires,just,later,Option.map_some,Option.some.injEq] using ok
        subst rs
        have cv := true_wire_keeps_the_header_and_fits_the_book keys h v just
        have ct := ih (fun x hx=>fits x (List.mem_cons_of_mem _ hx)) vs later
        refine ⟨by rw [List.length_cons,List.length_cons,ct.1],?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl|inside
        · exact ⟨cv.1 ▸ fits h List.mem_cons_self,cv.2⟩
        · exact ct.2 x inside

theorem paid_wire_gather_tariff_from_input_geometry {w U : ℕ} (keys : List (Word w))
    (reqs : List (WireRequest w)) (fit : RequestsFit reqs U) (rs : List WireRead)
    (ok : (emitWires keys reqs).result=some rs) (width : ℕ) :
    rawWireFee width rs≤reqs.length*(3*U+4*keys.length+width+12) := by
  obtain ⟨sz,dim⟩ := true_wire_tape_lengths keys reqs fit rs ok
  unfold rawWireFee
  refine (sum_map_cap rs (wireCharge width) _ ?_).trans_eq
    (congrArg (fun k=>k*(3*U+4*keys.length+width+12)) sz)
  intro row inside
  obtain ⟨h,l⟩ := dim row inside
  unfold wireCharge
  omega

private theorem read_depth_is_no_more_than_body (body : List Bool) (d : ℕ)
    (ok : (readDepthPrefix body).result=some d) : d≤body.length := by
  induction body generalizing d with
  | nil => simp [readDepthPrefix] at ok
  | cons b bs ih =>
    cases b
    · cases found : (readDepthPrefix bs).result with
      | none => simp [readDepthPrefix,found] at ok
      | some n =>
        have eq : n+1=d := by simpa only [readDepthPrefix,found,Option.map_some,Option.some.injEq] using ok
        exact eq ▸ Nat.succ_le_succ (ih n found)
    · have eq : 0=d := by simpa only [readDepthPrefix,Option.some.injEq] using ok
      exact eq ▸ Nat.zero_le _

theorem actual_request_depth_fits_header {w U : ℕ} (rs : List (WireRequest w))
    (h : RequestsFit rs U) (d : ℕ) (hit : (requestDepth rs).result=some d) : d≤U := by
  cases rs with
  | nil =>
    have eq : 0=d := by simpa only [requestDepth,Option.some.injEq] using hit
    exact eq ▸ Nat.zero_le U
  | cons a as =>
    exact (read_depth_is_no_more_than_body a.ancestry d hit).trans (h a List.mem_cons_self)

/-- Successful retained-page output of the original terminal compiler.
The retained address is not touched, and no separate wire list is supplied. -/
theorem actual_kept_packet_wire_tariff {w own key prec page U : ℕ}
    (old : Word own) (tag : Origin key prec page)
    (book : List (Word w)) (frames : List (FramedEdge w own key prec page))
    (fit : FramesFit frames U) (addr : Word key) (pg : Word page)
    (depth : ℕ) (wires : List WireRead)
    (read : (compileKeptPage old tag book frames).result=some (.packet addr pg depth wires))
    (a : ℕ) :
    depth≤U ∧ wires.length≤frames.length ∧
      rawWireFee (depth+a+2) wires≤frames.length*(3*U+4*book.length+(U+a+2)+12) := by
  let req := (collectRetained old frames).result
  obtain ⟨n,fitReq,_⟩ := retained_scan_bounded frames fit old
  cases pgHit : (copyOrigin tag).result.pageKey with
  | none => simp [compileKeptPage,pgHit] at read
  | some tok =>
    cases depthHit : (requestDepth req).result with
    | none => simp [compileKeptPage,pgHit,req,depthHit] at read
    | some d =>
      cases out : (emitWires book req).result with
      | none => simp [compileKeptPage,pgHit,req,depthHit,out] at read
      | some ws =>
        have eq : ReadCmd.packet (copyOrigin tag).result.stamp.creator tok d ws=.packet addr pg depth wires := by
          dsimp only [req] at depthHit out
          simpa only [compileKeptPage,pgHit,depthHit,out,Option.map_some,Option.some.injEq] using read
        have shape := ReadCmd.packet.inj eq
        obtain ⟨_,_,rfl,rfl⟩ := shape
        have h := actual_request_depth_fits_header req fitReq d depthHit
        have co := (true_wire_tape_lengths book req fitReq ws out).1
        exact ⟨h,co.trans_le n,(paid_wire_gather_tariff_from_input_geometry book req fitReq ws out _).trans
          (Nat.mul_le_mul n (by omega))⟩

theorem actual_fresh_packet_wire_tariff {w own key prec page U : ℕ}
    (addr : Word key) (book : List (Word w)) (frames : List (FramedEdge w own key prec page))
    (fit : FramesFit frames U) (pg : Word page) (depth : ℕ) (wires : List WireRead)
    (read : (compileFreshOne addr book frames pg).result=some (.packet addr pg depth wires))
    (a : ℕ) :
    depth=0 ∧ wires.length≤frames.length ∧
      rawWireFee (depth+a+2) wires≤frames.length*(3*U+4*book.length+(a+2)+12) := by
  let req := (scanFresh pg frames).result
  obtain ⟨n,fitReq,_⟩ := fresh_scan_bounded frames fit pg
  cases out : (emitWires book req).result with
  | none => simp [compileFreshOne,show (emitWires book (scanFresh pg frames).result).result=none from out] at read
  | some ws =>
    have eq : ReadCmd.packet addr pg 0 ws=.packet addr pg depth wires := by
      simpa only [compileFreshOne,copy_fixed_exact,
        show (emitWires book (scanFresh pg frames).result).result=some ws from out,
        Option.map_some,Option.some.injEq] using read
    obtain ⟨_,_,rfl,rfl⟩ := ReadCmd.packet.inj eq
    have co := (true_wire_tape_lengths book req fitReq ws out).1
    refine ⟨rfl,co.trans_le n,?_⟩
    rw [Nat.zero_add]
    exact (paid_wire_gather_tariff_from_input_geometry book req fitReq ws out (a+2)).trans
      (Nat.mul_le_mul_right _ n)
#print axioms true_wire_keeps_the_header_and_fits_the_book
#print axioms true_wire_tape_lengths
#print axioms paid_wire_gather_tariff_from_input_geometry
#print axioms actual_request_depth_fits_header
#print axioms actual_kept_packet_wire_tariff
#print axioms actual_fresh_packet_wire_tariff
end J6R66LeafTariff
