
import J6R51OnlineCore
import J6R50PeakStartPrecision

/-! Raw opaque-body width on the actual demanded source state. An
inherited body receives one bit; a born lane has two flag bits and the
actual fixed-width parent slot. No parsing of old unframed bytes or
envelope assumption for every possible future descriptor is used. -/
namespace J6R51Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost
open J6R10Repack J6R24MeteredRecursion J6R26DescriptorTree J6R34ChildPath
open J6R36ChildFramedRoute J6R41StructuredAllPaths
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R50Peak
open J6R50SourceProducer J6R51Online

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 3450

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}

theorem issued_lane_body_cap (X : StoredSite T v key prec tw bw page)
    (h : HalfAt T v) (col : Bool) (U : ℕ)
    (bound : ∀ x,(X.birth.native.physical.record x).body.length≤U) :
    (X.site.issuedLane h col).body.length≤max (U+1) (dim v+2) := by
  cases col
  · change ((false :: (X.birth.native.physical.record h.val).body) : List Bool).length≤_
    simp only [List.length_cons]
    exact (Nat.succ_le_succ (bound h.val)).trans (le_max_left _ _)
  · change (true :: (X.site.aux h.val).parentWasCol :: (X.site.aux h.val).parentSlot.bits).length≤_
    simp only [List.length_cons,(X.site.aux h.val).parentSlot.size]
    exact le_max_right _ _

def sourceBodyCap (s C seedWidth : ℕ) : ℕ :=
  max seedWidth (Nat.clog 2 s+2)+pathLimit s C

theorem actual_source_state_body_growth (M : OnlineMachine T key prec tw bw page q) (seedWidth : ℕ)
    (boot : ∀ (w : (Plan sel).Slot r) h,
      ((M.initial w).result.birth.native.physical.record h).body.length≤seedWidth)
    (p : Path sel r c) (w : (Plan sel).Slot c) (h : Port c.host.Edge) :
    ((sourceState M p w).birth.native.physical.record h).body.length≤
      max seedWidth (Nat.clog 2 s+2)+moves p := by
  induction p with
  | root =>
    change ((M.initial w).result.birth.native.physical.record h).body.length≤_
    simpa only [moves,Nat.add_zero] using (boot w h).trans
      (le_max_left seedWidth (Nat.clog 2 s+2))
  | @step y p u ih =>
    let X := sourceState M p u
    let K := (M.demand X w).result
    have exactBody := K.advance.exactBody h
    change ((sourceState M (.step p u) w).birth.native.physical.record h).body =
      (X.site.issuedLane (childHalves T (p.ticket u) (edge h)) (side h)).body at exactBody
    rw [exactBody]
    let L := max seedWidth (Nat.clog 2 s+2)
    have prev : ∀ x,(X.birth.native.physical.record x).body.length≤L+moves p := ih u
    have step := issued_lane_body_cap X (childHalves T (p.ticket u) (edge h)) (side h) _ prev
    have dimCap : dim (p.ticket u)≤Nat.clog 2 s := bits_le_lam _ _
    have leL : Nat.clog 2 s+2≤L := le_max_right _ _
    refine step.trans (max_le ?_ ?_)
    · simp only [moves]
      omega
    · simp only [moves]
      omega

theorem actual_demanded_body_fits (M : OnlineMachine T key prec tw bw page q) (seedWidth : ℕ)
    (boot : ∀ (w : (Plan sel).Slot r) h,
      ((M.initial w).result.birth.native.physical.record h).body.length≤seedWidth)
    (p : Path sel r c) (w : (Plan sel).Slot c) (h : Port c.host.Edge) :
    ((borns M p w).native.physical.record h).body.length≤sourceBodyCap s C seedWidth :=
  (actual_source_state_body_growth M seedWidth boot p w h).trans
    (Nat.add_le_add_left (actual_ancestry_moves_any_start cfg sel T.rootStable p) _)

#print axioms issued_lane_body_cap
#print axioms actual_source_state_body_growth
#print axioms actual_demanded_body_fits
end J6R51Peak
