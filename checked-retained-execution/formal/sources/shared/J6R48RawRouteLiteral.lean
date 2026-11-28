import J6R48RawRoutePhysical

/-! Group words are read from the real next packing's page/slot table,
not supplied by a separate port-to-group oracle. -/
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
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

theorem literal_seat_names_group {E Row Col : Type} {N : Network E Row Col} {a k : ℕ}
    (P : PhysicalPacking N a (Fin 64)) (i : Fin a)
    (code : Page a P.copies (Fin 64)→Word k) (x : Port E) :
    (groupOf (physicalSeatField P i code) x).val=
      (retainedGroup N (atGroup P i) x).val := by
  cases x with
  | inl e =>
    change (word (q:=6) (rowGroup P.mask i (P.seat e)).val).val=_
    rw [word_val (rowGroup P.mask i (P.seat e)).isLt,row_symbol]
    rfl
  | inr e =>
    change (word (q:=6) (colGroup P.mask i (P.seat e)).val).val=_
    rw [word_val (colGroup P.mask i (P.seat e)).isLt,col_symbol]
    rfl

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)

def rawLiteralNextSeats {k : ℕ} (S : SiteInputs Q previous)
    (d : J6R12Blueprint.Ready SP (sourceDelta s) v.child) (t : J6ActiveRun.Center SP v.child)
    (code : Page A (packing sel d).copies (Fin 64)→Word k)
    (raw : List (SeatField A k))
    (same : raw=(childOrder S).map (physicalSeatField (packing sel d) (centerIndex d t) code)) :
    NextSeats (childOrder S) A k :=
  ⟨raw,physicalSeatField (packing sel d) (centerIndex d t) code,same⟩

theorem literal_next_groups {k : ℕ} (S : SiteInputs Q previous)
    (d : J6R12Blueprint.Ready SP (sourceDelta s) v.child) (t : J6ActiveRun.Center SP v.child)
    (code : Page A (packing sel d).copies (Fin 64)→Word k)
    (raw : List (SeatField A k))
    (same : raw=(childOrder S).map (physicalSeatField (packing sel d) (centerIndex d t) code))
    (x : Port v.child.host.Edge) :
    (groupOf (rawLiteralNextSeats S d t code raw same).seat x).val=(physicalGroup sel d t x).val :=
  literal_seat_names_group (packing sel d) (centerIndex d t) code x

def actualNextPhysical {k : ℕ} (S : SiteInputs Q previous)
    (d : J6R12Blueprint.Ready SP (sourceDelta s) v.child) (t : J6ActiveRun.Center SP v.child)
    (code : Page A (packing sel d).copies (Fin 64)→Word k)
    (raw : List (SeatField A k))
    (same : raw=(childOrder S).map (physicalSeatField (packing sel d) (centerIndex d t) code)) :
    Meter (PhysicalPorts sel d t (Q.port+1)) :=
  let L := rawLiteralNextSeats S d t code raw same
  ⟨emittedPhysical S d t L (literal_next_groups S d t code raw same),(emitNext S L).steps⟩

theorem physically_generated_child_keeps_route {k : ℕ} (S : SiteInputs Q previous)
    (d : J6R12Blueprint.Ready SP (sourceDelta s) v.child) (t : J6ActiveRun.Center SP v.child)
    (code : Page A (packing sel d).copies (Fin 64)→Word k)
    (raw : List (SeatField A k))
    (same : raw=(childOrder S).map (physicalSeatField (packing sel d) (centerIndex d t) code))
    (x : Port v.child.host.Edge) :
    let out := actualNextPhysical S d t code raw same
    (out.result.record x).body=(S.issuedLane (childHalves T v (edge x)) (side x)).body ∧
      (out.result.record x).group.val=(physicalGroup sel d t x).val ∧
      (out.result.record x).address=childHalfKey (childKey T v Q.native.physical (edge x)) (side x) ∧
      out.steps=6+((childOrder S).map (fun e=>framedCopiesFee (frameOf S e)+3*A+3*k+8)).sum :=
  ⟨rfl,literal_next_groups S d t code raw same x,next_record_address S _ x,
    (emit_next_exact S _).2⟩

#print axioms literal_seat_names_group
#print axioms literal_next_groups
#print axioms physically_generated_child_keeps_route
end
end J6R48RawRoute

