import J6R49SourceLayoutOrder
import J6R55TerminalOriginSite

/-! Scan the actual ordered paired half-port record bank and the real
one-seat-per-edge bank in lockstep. Copy both distinct key words and
one shared seat payload per physical edge. A malformed lockstep input
returns none; the typed source handoff proves that it cannot occur. -/
namespace J6R64.BootSeats
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R31RootResidentTables J6R32ChildResidentTransfer J6R48RawRoute
open J6OrientedHost J6R10Repack J6R20Ancestor J6R26DescriptorTree J6R36ChildFramedRoute J6R24MeteredRecursion
open J6R25PreparedSupply J6R30ProducedGateRegistry J6R35RootOrigins
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

def pairStride (w a p : ℕ) : ℕ := 6*w+3*(a+p)+61

def writePairs {w a p : ℕ} :
    List (PortRow w) → List (SeatField a p) → Meter (Option (List (RefRow w (SeatField a p))))
  | [],[] => ⟨some [],3⟩
  | left::right::tail, seat::later =>
    let L := copyFixed left.address
    let R := copyFixed right.address
    let S := copySeat seat
    let out := writePairs tail later
    ⟨out.result.map (fun rest =>
        (⟨L.result,S.result⟩ : RefRow w (SeatField a p)) :: ⟨R.result,S.result⟩ :: rest),
      L.steps+R.steps+S.steps+out.steps+13⟩
  | _,_ => ⟨none,3⟩

theorem write_pairs_exact {E : Type} {w a p : ℕ} (xs : List E)
    (native : Port E → PortRow w) (seat : E → SeatField a p) :
    writePairs ((pairedPorts xs).map native) (xs.map seat)=
      ⟨some ((pairedPorts xs).map (fun h=>⟨(native h).address,seat (edge h)⟩)),
        3+pairStride w a p*xs.length⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have step : pairedPorts (x::xs)=(Sum.inl x)::(Sum.inr x)::pairedPorts xs := rfl
    simp only [step,List.map_cons,writePairs,copy_fixed_exact,copied_seat_exact,ih,Option.map_some,
      edge,Sum.elim_inl,Sum.elim_inr,List.length_cons,pairStride,Nat.mul_succ]
    congr 1
    omega

def lookupRecordBits {w a p : ℕ} (r : RefRow w (SeatField a p)) : ℕ :=
  r.address.bits.length+r.payload.slot.bits.length+r.payload.page.bits.length+
    r.payload.rowGroup.bits.length+r.payload.colGroup.bits.length

theorem lookup_record_width {w a p : ℕ} (r : RefRow w (SeatField a p)) :
    lookupRecordBits r=w+a+p+12 := by
  rw [lookupRecordBits,r.address.size,r.payload.slot.size,r.payload.page.size,
    r.payload.rowGroup.size,r.payload.colGroup.size]

theorem serialized_lookup_table_size {w a p : ℕ} (l : List (RefRow w (SeatField a p))) :
    (l.map lookupRecordBits).sum=(w+a+p+12)*l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,lookup_record_width,ih,Nat.mul_succ]
    omega

#print axioms writePairs
#print axioms write_pairs_exact
#print axioms lookup_record_width
#print axioms serialized_lookup_table_size
end J6R64.BootSeats
