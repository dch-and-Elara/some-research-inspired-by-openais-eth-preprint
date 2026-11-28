import J6R58OrdinalSpaceNativeLoad
import J6R58OrdinalSpaceEventUnique

/-! Descendant request operands have no list of all legal tuples and
no supplied LocalLoad. The raw exponent words and the mode ordinal
come from the current cursor. The original checked event and original
acceptor are then executed for the same physical packet. -/
namespace J6R63Ordinal
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R24MeteredRecursion J6R26DescriptorTree J6R32StatefulArithmetic
open J6R50SourceProducer J6R51Online J6R51Dispatch J6R52Dispatch J6R53Dispatch
open J6R58OrdinalSpace
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 3850
set_option maxHeartbeats 8000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
variable {w : (Plan sel).Slot v.child}
local notation "nx" => (J6R48RawRoute.successorTicket v w)
local notation "dt" => (ticketReady T (J6R48RawRoute.successorTicket v w))
local notation "ct" => (Ticket.centerAt (J6R48RawRoute.successorTicket v w))
variable (I : SiteTape sel (ticketReady T (J6R48RawRoute.successorTicket v w))
  (Ticket.centerAt (J6R48RawRoute.successorTicket v w)) (q+1))

structure Request (I : SiteTape sel (ticketReady T (J6R48RawRoute.successorTicket v w))
    (Ticket.centerAt (J6R48RawRoute.successorTicket v w)) (q+1)) where
  selection : ExplicitSelectedWords X.site w q
  replay : Replayed X.site w q selection
  roster : List (RawMode (q+1))
  trueRoster : roster=I.modes.map (encodeMode (centerIndex dt ct))
  tc : ℕ
  tz : ℕ
  tWord : Word tc
  zWord : Word tz
  gWord : Word 6
  trueT : tWord.val=centerOrdinal T nx
  trueZ : zWord.val=(nx).probeAt.val
  trueG : gWord.val=(nx).groupAt.val
  shell : PayloadShell replay
  directory : DirectorySeed replay shell

variable {I} {b : ℕ}
variable {raw : List (Word (q+1))} {i : Word b}

def Request.current (A : Request (X:=X) (w:=w) (q:=q) I)
    (raw : List (Word (q+1))) (i : Word b)
    (rawExact : raw.map Word.val=vectorKey sel dt ct I (nx).modeAt)
    (rankExact : i.val=modeOrdinal T nx) : RankedEventFields A.replay raw :=
  { tape := I
    exponents := rawExact
    roster := A.roster
    rosterExact := A.trueRoster
    tc := A.tc
    tz := A.tz
    tm := b
    centre := A.tWord
    probe := A.zWord
    group := A.gWord
    ordinal := i
    centreExact := A.trueT
    probeExact := A.trueZ
    groupExact := A.trueG
    ordinalExact := rankExact }

def acceptCurrent (req : Meter (Request (X:=X) (w:=w) (q:=q) I))
    (raw : List (Word (q+1))) (i : Word b)
    (rawExact : raw.map Word.val=vectorKey sel dt ct I (nx).modeAt)
    (rankExact : i.val=modeOrdinal T nx) : Meter (LocalLoad X w) :=
  let A := req.result
  let terminal := loadUsingOrdinal (A.current raw i rawExact rankExact) A.shell A.directory
  ⟨terminal.result,req.steps+terminal.steps+4⟩

#print axioms Request.current
#print axioms acceptCurrent
end
end J6R63Ordinal
