import J6R53DispatchOnlineReuse

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 11500000
set_option maxRecDepth 2950
set_option linter.unusedSectionVars false

/-! A small routed payload that reuses the existing checked forwarded
LocalLoad. Its raw argument is the actual external mode word; the route
is not allowed to silently substitute a different retained vector. -/
namespace J6R54Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion J6R32StatefulArithmetic
open J6R30ProducedGateRegistry J6R33StatefulArithmeticPage J6R48DFS
open J6R50SourceProducer J6R51Online J6R52Dispatch J6R53Dispatch
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (X : StoredSite T v key prec tw bw page)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "Slots" => ((Plan sel).Slot v.child)
local notation "Bank" => (PageBank f ell key prec tw bw page)
local notation "Job" => (PageJob f ell key prec tw bw page)

/-- An admitted provider returns checked, already retained bytes,
not an already executed child result. -/
structure RetainedTicket (raw : List (Word q)) where
  w : Slots
  packet : ForwardedPacket X w
  sameRaw : HEq packet.raw raw

def RetainedReader (X : StoredSite T v key prec tw bw page) (q : ℕ) :=
  ∀ (raw : List (Word q)),Fin 64→Meter (Option (RetainedTicket X raw))

variable {X}

def RetainedTicket.localLoad {raw : List (Word q)} (u : RetainedTicket X raw) : Meter (LocalLoad X u.w) :=
  u.packet.load

def rawCallback {Y : Type}
    (select : RetainedReader X q) (retire : Job→ℕ)
    (go : (w : Slots)→StoredSite T (J6R48RawRoute.successorTicket v w) key prec tw bw page → SM Bank Y)
    (fallback : Meter Y) (bank : Bank) (raw : List (Word q)) (g : Fin 64) : Meter Y :=
  let found := select raw g
  match found.result with
  | none => ⟨fallback.result,found.steps+fallback.steps+3⟩
  | some row =>
    let out := openDemand row.localLoad retire (go row.w) fallback bank
    ⟨out.result.1,found.steps+out.steps+4⟩

theorem raw_callback_selects_exact_load {Y : Type}
    (select : RetainedReader X q) (retire : Job→ℕ)
    (go : (w : Slots)→StoredSite T (J6R48RawRoute.successorTicket v w) key prec tw bw page → SM Bank Y)
    (fallback : Meter Y) (bank : Bank) (raw : List (Word q)) (g : Fin 64)
    (row : RetainedTicket X raw) (got : (select raw g).result=some row) :
    let out := openDemand row.localLoad retire (go row.w) fallback bank
    rawCallback select retire go fallback bank raw g=
      ⟨out.result.1,(select raw g).steps+out.steps+4⟩ := by
  simp only [rawCallback,got]

#print axioms RetainedTicket.localLoad
#print axioms rawCallback
#print axioms raw_callback_selects_exact_load
end
end J6R54Dispatch

