
import J6R30ProducedGateRegistryInvoke
import J6R27OriginalGateCapsuleJoin

/-! Raw, resident R27 input ABI. Compilation is the actual R27 program:
slot scan, sparse native mode expansion and bit-probe construction.
The only optional value passed to the publisher is this program's real
output. It is not an independently supplied typed OriginFields. -/
namespace J6R30ProducedGateRegistry
open AOracleMachineTime A1R10 J6R21Ancestor J6R27OriginalGate J6R17ModeTape

structure Frames {p : ℕ} (fw : List (A1R10.Word p)) (a q codew pagew : ℕ) where
  axis : List Bool
  owner : PageRef q
  group : J6R15ModeCost.Word 6
  start : J6R15ModeCost.Word codew
  raw : List (RawMode q)
  sparse : List (RawMode q×J6R15ModeCost.Word q)
  masks : List (MaskRow q)
  seatKey : J6R15ModeCost.Word pagew
  seats : List (SeatField a pagew)
  coordinates : {b : List Bool // b.length=fw.length}

def Frames.compile {a p ell q codew pagew : ℕ} {old : List (A1R10.Word p)} {i : Fin a}
    (R : Frames old a q codew pagew) (pPos : 0<p) (vPos : 0<ell) (fit : i.val+1≤q) :
    Meter (Option (OriginFields a p ell q old i)) :=
  let slots := selectedSlots R.seatKey R.group R.seats
  let modes := compileModes i p fit R.axis R.owner R.group R.start R.raw R.sparse R.masks
  assembleFromProbeBits pPos vPos R.coordinates slots modes

def publishFrames {p ell a q codew pagew key prec tw bw : ℕ} {old : List (A1R10.Word p)} {i : Fin a}
    (B : GateLedger (ell:=ell) (w:=q) old i key prec tw bw)
    (entry : Meter (DirRow key)) (offset : ℕ) (ctx : CentreContext tw bw)
    (R : Frames old a q codew pagew) (pPos : 0<p) (vPos : 0<ell) (fit : i.val+1≤q) :
    Meter (GateLedger (ell:=ell) (w:=q) old i key prec tw bw×Bool) :=
  publishCompiled B entry offset ctx (R.compile pPos vPos fit)

end J6R30ProducedGateRegistry

