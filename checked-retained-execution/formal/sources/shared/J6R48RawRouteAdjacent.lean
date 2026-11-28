import J6R48RawRouteLiteral
import J6R48RawRouteOccurrence
import J6R41StructuredAllPathsStream

/-! The generated physical file is retained by the original adjacent
occurrence compiler. The R41 copied-body equality is a conclusion. -/
namespace J6R48RawRoute
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R34RootAtlas J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 7500000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)

def successorTicket (v : Ticket sel r) (u : (Plan sel).Slot v.child) : Ticket sel r :=
  ⟨v.child,reach_snoc (Plan sel) v.path v.slot,u⟩

theorem successor_ticket_is_actual_path
    {c : Call (PhysicalHost f ell)} (p : J6R32StatefulArithmetic.Path sel r c)
    (w : (Plan sel).Slot c) (u : (Plan sel).Slot (p.ticket w).child) :
    successorTicket (p.ticket w) u=(J6R32StatefulArithmetic.Path.step p w).ticket u := rfl

variable {v : Ticket sel r} {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)

structure LiteralAdjacent (S : SiteInputs Q previous) (u : (Plan sel).Slot v.child) (k : ℕ) where
  code : Page A (packing sel (ticketReady T (successorTicket v u))).copies (Fin 64)→Word k
  raw : List (SeatField A k)
  exact : raw=(childOrder S).map (physicalSeatField
    (packing sel (ticketReady T (successorTicket v u)))
    (centerIndex (ticketReady T (successorTicket v u)) (successorTicket v u).centerAt) code)

def LiteralAdjacent.generated {k : ℕ} {S : SiteInputs Q previous} {u : (Plan sel).Slot v.child}
    (D : LiteralAdjacent S u k) : Meter (PhysicalFile T (successorTicket v u) (Q.port+1)) :=
  actualNextPhysical S (ticketReady T (successorTicket v u)) (successorTicket v u).centerAt
    D.code D.raw D.exact

def LiteralAdjacent.nextInput {k : ℕ} {S : SiteInputs Q previous} {u : (Plan sel).Slot v.child}
    (D : LiteralAdjacent S u k) (I : OccurrenceInput T (successorTicket v u) key prec tw bw page) :
    OccurrenceInput T (successorTicket v u) key prec tw bw page :=
  replaceOccurrencePhysical I D.generated

theorem genuine_adjacent_birth_actual_body {k : ℕ}
    {S : SiteInputs Q previous} {u : (Plan sel).Slot v.child}
    (D : LiteralAdjacent S u k) (I : OccurrenceInput T (successorTicket v u) key prec tw bw page)
    (x : Port v.child.host.Edge) :
    ((compileOccurrence (D.nextInput I)).native.physical.record x).body=
      (S.issuedLane (childHalves T v (edge x)) (side x)).body := by
  exact compiled_replaced_row_body I D.generated x

theorem genuine_adjacent_birth_exact_file_and_meter {k : ℕ}
    {S : SiteInputs Q previous} {u : (Plan sel).Slot v.child}
    (D : LiteralAdjacent S u k) (I : OccurrenceInput T (successorTicket v u) key prec tw bw page) :
    let born := compileOccurrence (D.nextInput I)
    birthPhysical born=⟨Q.port+1,D.generated.result⟩ ∧
      born.job.identifier=I.issued.result ∧
      born.job.immutable.payload.stamp.created.val=(successorTicket v u).child.prec ∧
      born.issuance.steps=I.issued.steps+
        (I.native.steps+D.generated.steps+4+I.physical.steps+I.words.steps+4) :=
  generated_occurrence_has_no_old_physical_input I D.generated

section PathCopy
variable {born : Births T key prec tw bw page}
variable {keys : PageKeys born} {rootTags : r.host.Row⊕r.host.Col→Origin key prec page}

theorem actual_path_adjacent_body_link
    (files : SiteFiles born keys rootTags) (rootPorts : Port r.host.Edge→Payload key prec page)
    {c : Call (PhysicalHost f ell)} (p : J6R32StatefulArithmetic.Path sel r c)
    (w : (Plan sel).Slot c) (u : (Plan sel).Slot (p.ticket w).child) {k : ℕ}
    (D : LiteralAdjacent (files p w) u k)
    (I : OccurrenceInput T (successorTicket (p.ticket w) u) key prec tw bw page)
    (x : Port (p.ticket w).child.host.Edge) :
    ((compileOccurrence (D.nextInput I)).native.physical.record x).body=
      (publishedPayload files rootPorts (.step p w) x).2 :=
  genuine_adjacent_birth_actual_body D I x

end PathCopy
#print axioms successor_ticket_is_actual_path
#print axioms genuine_adjacent_birth_actual_body
#print axioms genuine_adjacent_birth_exact_file_and_meter
#print axioms actual_path_adjacent_body_link
end
end J6R48RawRoute

