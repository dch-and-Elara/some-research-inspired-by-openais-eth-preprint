import J6R49SourceLayoutDescend
import J6R48RawRouteSourceInput
import J6R32ChildResidentTransferSelector

/-! Install the paid result only at the actual same selected chart.
The raw next-seat stream is not an external field of this adapter.
Changing to the produced chart is possible before constructing the
successor plan; it is not an identification of different packings. -/
namespace J6R49SourceLayout
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes J6R11Repack
open J6R32ChildResidentTransfer J6R48RawRoute J6R33GeneratedChildSite
open J6R34RootAtlas
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 10200000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable {S : SiteInputs Q previous}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)
variable {q : ℕ} {u : (Plan sel).Slot v.child}
local notation "next" => (successorTicket v u)
local notation "d" => (ticketReady T (successorTicket v u))
local notation "t" => (Ticket.centerAt (successorTicket v u))


def installed_chart_for_selector
    {out : Meter (Option (PreparedSeats ((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth) q))}
    (X : GeneratedChild (q:=q) S d t out) (choose : X.chart=packing sel d) :
    ResidentReceipt (packing sel d) (centerIndex d t) (registerPrecision SP v.child t) X.data.native :=
  choose ▸ X.receipt

def adjacentOfGenerated
    {out : Meter (Option (PreparedSeats ((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth) q))}
    (X : GeneratedChild (q:=q) S d t out) (choose : X.chart=packing sel d) :
    LiteralAdjacent S u ((q-A)+13*A) where
  code := childPageKey (q-A)
  raw := X.data.ordered
  exact := X.ordered.trans (congrArg (fun P=>
    (childOrder S).map (physicalSeatField P (centerIndex d t) (childPageKey (q-A)))) choose)

/-- The direct byte join consumes the verified, finite optional
output, not projections of a Classical.choice packing. The predecessor
frame has already been written; this is the incremental fee. -/
def emitFromPrepared {a q : ℕ} (setup : Meter (Option (PreparedSeats a q)))
    {w owner key prec page : ℕ}
    (frames : Option (List (FramedEdge w owner key prec page))) :
    Meter (Option (List (PortRow (w+1)))) :=
  match setup.result,frames with
  | some resolved,some rows =>
    let W := writeNextRows rows resolved.ordered
    ⟨W.result,setup.steps+W.steps+5⟩
  | _,_ => ⟨none,setup.steps+3⟩

theorem emitted_from_the_actual_prepared_port_tape
    {out : Meter (Option (PreparedSeats ((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth) q))}
    (X : GeneratedChild (q:=q) S d t out) (choose : X.chart=packing sel d) :
    let D := adjacentOfGenerated (q:=q) (u:=u) X choose
    let W := emitFromPrepared out S.write.result.framed
    W.result=some D.generated.result.raw ∧
      W.steps=out.steps+D.generated.steps+3 := by
  let L := adjacentOfGenerated (q:=q) (u:=u) X choose
  let st := rawLiteralNextSeats S d t L.code L.raw L.exact
  have hs := emit_next_exact S st
  have w : (writeNextRows ((childOrder S).map (frameOf S)) X.data.ordered).result =
      some (L.generated.result.raw) := by
    change _=some ((emitNext S st).result.getD [])
    have eq : (emitNext S st).result=
        (writeNextRows ((childOrder S).map (frameOf S)) X.data.ordered).result := by
      unfold emitNext
      rw [source_framed_in_child_order S]
      rfl
    rw [←eq,hs.1]
    rfl
  unfold emitFromPrepared
  rw [X.success,source_framed_in_child_order S]
  dsimp only
  refine ⟨w,?_⟩
  change out.steps+(writeNextRows ((childOrder S).map (frameOf S)) X.data.ordered).steps+5 =
    out.steps+(emitNext S st).steps+3
  unfold emitNext
  rw [source_framed_in_child_order S]
  dsimp only
  rw [show st.rows=X.data.ordered from rfl]
  omega

theorem generated_layout_birth_copies_same_predecessor_body
    {out : Meter (Option (PreparedSeats ((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth) q))}
    (X : GeneratedChild (q:=q) S d t out) (choose : X.chart=packing sel d)
    (words : OccurrenceWordsOnly T next key prec tw bw page)
    (x : Port v.child.host.Edge) :
    let D := adjacentOfGenerated (q:=q) (u:=u) X choose
    ((compileOccurrence (words.bind D.generated)).native.physical.record x).body=
      (S.issuedLane (childHalves T v (edge x)) (side x)).body :=
  next_source_words_realize_adjacent_route (S:=S) (u:=u) (adjacentOfGenerated (q:=q) (u:=u) X choose) words x

/-- If the selector has not yet been constructed for this home call,
    the exact new chart can be installed there without changing any
    shallower parent chart. This is a proof-side selector operation,
    not a metered pass over the earlier tree. -/
theorem new_chart_selection_does_not_change_shallower_hosts
    {out : Meter (Option (PreparedSeats ((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth) q))}
    (X : GeneratedChild (q:=q) S d t out)
    {c : Call (PhysicalHost f ell)} (dc : Ready SP (sourceDelta s) c)
    (earlier : c.depth<v.child.depth) :
    packing (oneSiteSelector sel v.child X.chart) d=X.chart ∧
    packing (oneSiteSelector sel v.child X.chart) dc=packing sel dc := by
  refine ⟨one_site_exact sel v.child X.chart d,other_site_unchanged sel v.child X.chart dc ?_⟩
  intro eq
  exact Nat.ne_of_lt earlier (congrArg Call.depth eq)

#print axioms installed_chart_for_selector
#print axioms emitted_from_the_actual_prepared_port_tape
#print axioms generated_layout_birth_copies_same_predecessor_body
#print axioms new_chart_selection_does_not_change_shallower_hosts
end
end J6R49SourceLayout