import J6R52DispatchShell

/-! The next directory consumes the same already held, paid selected
seat tape that drives the real replay. No second seat file or second
placement is a supplier field. The remaining owner/address reads are
local to the current scoped call. -/
namespace J6R58RequestSource
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R27OriginalGate
open P11FullPacking J6R9PacketScopes J6R10Repack J6R12CollisionEdges
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R33GeneratedChildSite
open J6R34ChildPath J6R41StructuredAllPaths J6R48GeneratedAddons J6R48RawRoute
open J6R30ProducedGateRegistry J6R32ChildResidentTransfer J6R33StatefulArithmeticPage
open J6R49SourceLayout J6R50SourceProducer J6R51Online J6R52Dispatch
open J6R21Ancestor J6R36ChildFramedRoute J6R34RootAtlas
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4200
set_option Elab.async false

def reindexSeatWidth {k a b c : ℕ} (h : b=c) (l : List (RefRow k (SeatField a b))) :
    List (RefRow k (SeatField a c)) := h ▸ l

theorem reindex_physical_seat_rows {E L R : Type} {N : Network E L R} {a b c k : ℕ}
    (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (code : Page a P.copies (Fin 64)→Word b)
    (key : E→Word k) (l : List E) (h : b=c) :
    reindexSeatWidth h (l.map (fun e=>⟨key e,physicalSeatField P i code e⟩))=
      l.map (fun e=>⟨key e,physicalSeatField P i (fun g=>h ▸ code g) e⟩) := by
  cases h
  rfl

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable {X : StoredSite T v key prec tw bw page} {u : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site u q}
variable (R : Replayed X.site u q U)
local notation "Λ" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)
local notation "nx" => (successorTicket v u)
local notation "Edge" => v.child.host.Edge
local notation "Name" => (childKey T v X.birth.native.physical)
local notation "ReadyNext" => (ticketReady T (successorTicket v u))
local notation "Here" => (Ticket.centerAt (successorTicket v u))

def directorySeatRows (B : PayloadShell R) :
    List (RefRow X.birth.port (SeatField (dim nx) page)) :=
  reindexSeatWidth B.width U.rows

theorem directory_seats_exact_order (B : PayloadShell R) :
    directorySeatRows R B=
      U.edges.map (fun e=>⟨Name e,physicalSeatField (layout T nx) (axis T nx) (shellPageWord R B) e⟩) := by
  unfold directorySeatRows
  rw [U.edgesExact]
  exact reindex_physical_seat_rows (packing sel ReadyNext) (centerIndex ReadyNext Here)
    (childPageKey (q-A)) Name U.edges B.width

theorem held_seats_length (B : PayloadShell R) :
    (directorySeatRows R B).length=U.rows.length := by
  rw [directory_seats_exact_order R B,List.length_map,U.edgesExact,List.length_map]

theorem held_seats_hit_and_unique (B : PayloadShell R) (e : Edge) :
    let s := physicalSeatField (layout T nx) (axis T nx) (shellPageWord R B) e
    (⟨Name e,s⟩ : RefRow X.birth.port (SeatField (dim nx) page))∈directorySeatRows R B ∧
      ∀ row∈directorySeatRows R B,row.address=Name e → row.payload=s := by
  dsimp only
  rw [directory_seats_exact_order R B]
  constructor
  · exact List.mem_map.mpr ⟨e,U.all e,rfl⟩
  · intro row member hit
    obtain ⟨other,_,rfl⟩ := List.mem_map.mp member
    have same : other=e := child_key_injective T v X.birth.native.physical hit
    rw [same]

#print axioms reindex_physical_seat_rows
#print axioms directory_seats_exact_order
#print axioms held_seats_length
#print axioms held_seats_hit_and_unique
end
end J6R58RequestSource
