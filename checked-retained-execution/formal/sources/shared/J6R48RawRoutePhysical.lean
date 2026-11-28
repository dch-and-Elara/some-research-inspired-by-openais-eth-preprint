import J6R48RawRouteFrame

/-! Produce the next typed physical file from the real previous framing
and the next chart's resident seat rows; no next-file body premise. -/
namespace J6R48RawRoute
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3000
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

structure NextSeats {E : Type} (order : List E) (a k : ℕ) where
  rows : List (SeatField a k)
  seat : E→SeatField a k
  source : rows=order.map seat

def groupOf {E : Type} {a k : ℕ} (seat : E→SeatField a k) (p : Port E) : Word 6 :=
  match p with
  | .inl e=>(seat e).rowGroup
  | .inr e=>(seat e).colGroup

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs Q previous)
local notation "E" => (v.child.host.Edge)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
variable {a k : ℕ}

def nextRecord (S : SiteInputs Q previous) (seat : E→SeatField a k) (p : Port E) :
    PortRow (Q.port+1) :=
  nextPortView (side p) (groupOf seat p) (S.issuedLane (childHalves T v (edge p)) (side p))

theorem record_has_same_lane_body (seat : E→SeatField a k) (p : Port E) :
    (nextRecord S seat p).body =
      (S.issuedLane (childHalves T v (edge p)) (side p)).body := rfl

theorem next_record_address (seat : E→SeatField a k) (p : Port E) :
    (nextRecord S seat p).address=childHalfKey
      (childKey T v Q.native.physical (edge p)) (side p) := by
  cases p <;> rfl

theorem next_record_key_inj (seat : E→SeatField a k) :
    Function.Injective (fun p : Port E=>(nextRecord S seat p).address) := by
  intro p q eq
  change (nextRecord S seat p).address=(nextRecord S seat q).address at eq
  rw [next_record_address,next_record_address] at eq
  have pair : (childKey T v Q.native.physical (edge p),side p)=
      (childKey T v Q.native.physical (edge q),side q) := child_half_key_injective eq
  have e := child_key_injective T v Q.native.physical (congrArg Prod.fst pair)
  have b := congrArg Prod.snd pair
  cases p <;> cases q
  · exact congrArg Sum.inl e
  · exact Bool.noConfusion b
  · exact Bool.noConfusion b
  · exact congrArg Sum.inr e

/-- Consumes the already written predecessor framing; no second fee
for producing the old descriptor is included here. -/
def emitNext (L : NextSeats (childOrder S) a k) : Meter (Option (List (PortRow (Q.port+1)))) :=
  match S.write.result.framed with
  | none=>⟨none,2⟩
  | some frames=>
    let W := writeNextRows frames L.rows
    ⟨W.result,W.steps+2⟩

theorem emit_next_exact (L : NextSeats (childOrder S) a k) :
    (emitNext S L).result=
      some ((pairedPorts (childOrder S)).map (nextRecord S L.seat)) ∧
    (emitNext S L).steps=
      6+((childOrder S).map (fun e=>framedCopiesFee (frameOf S e)+3*a+3*k+8)).sum := by
  unfold emitNext
  rw [source_framed_in_child_order S,L.source]
  obtain ⟨read,pay⟩ := write_next_rows_exact (childOrder S) (frameOf S) L.seat
  refine ⟨read.trans ?_,?_⟩
  · congr 1
    rw [pairedPorts,List.map_flatMap]
    rfl
  · dsimp only
    omega

def emittedPhysical (S : SiteInputs Q previous)
    (d : J6R12Blueprint.Ready SP (sourceDelta s) v.child) (t : Center SP v.child)
    (L : NextSeats (childOrder S) a k)
    (groups : ∀ p : Port E,(groupOf L.seat p).val=(physicalGroup sel d t p).val) :
    PhysicalPorts sel d t (Q.port+1) where
  raw := (emitNext S L).result.getD []
  order := pairedPorts (childOrder S)
  nodup := paired_ports_nodup _ (child_order_complete S).1
  complete p := (mem_paired_ports p _).mpr ((child_order_complete S).2 (edge p))
  record := nextRecord S L.seat
  source := by rw [(emit_next_exact S L).1]; rfl
  labelled := groups
  distinct := next_record_key_inj S L.seat

theorem newly_emitted_physical_keeps_body (S : SiteInputs Q previous)
    (d : J6R12Blueprint.Ready SP (sourceDelta s) v.child) (t : Center SP v.child)
    (L : NextSeats (childOrder S) a k)
    (groups : ∀ p : Port E,(groupOf L.seat p).val=(physicalGroup sel d t p).val) (p : Port E) :
    ((emittedPhysical S d t L groups).record p).body=
      (S.issuedLane (childHalves T v (edge p)) (side p)).body := rfl

#print axioms record_has_same_lane_body
#print axioms next_record_address
#print axioms next_record_key_inj
#print axioms emit_next_exact
#print axioms newly_emitted_physical_keeps_body
end
end J6R48RawRoute

