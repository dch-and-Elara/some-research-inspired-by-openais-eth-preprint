import J6R58BootScopeBits
import J6R55TerminalOriginSite
import J6R53OldOwnerTape

/-! Raw boot words already resident after a paid common prefix can be
read by concrete scans and copies. The descriptor pointer is resolved
from a true tagged row; this does not instantiate/precompute a free
scope catalogue. -/
namespace J6R58BootScope
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R53OldOwner J6R49SourceLayout
open J6R51Peak J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11000000
set_option Elab.async false

def copyBootHeaders {w : ℕ} :
    List (OwnerGroup w)→Meter (List (OwnerGroup w))
  | [] => ⟨[],3⟩
  | x::xs =>
    let k := copyFixed x.key
    let g := copyFixed x.group
    let tail := copyBootHeaders xs
    ⟨⟨k.result,g.result⟩::tail.result,k.steps+g.steps+tail.steps+6⟩

theorem copy_boot_headers_exact {w : ℕ} (xs : List (OwnerGroup w)) :
    copyBootHeaders xs=⟨xs,3+(3*w+26)*xs.length⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨k,g⟩
    simp only [copyBootHeaders,copy_fixed_exact,ih,List.length_cons,Nat.mul_succ]
    congr 1
    omega

def copyBootSeatRows {w d pg : ℕ} :
    List (RefRow w (SeatField d pg))→Meter (List (RefRow w (SeatField d pg)))
  | [] => ⟨[],3⟩
  | x::xs =>
    let k := copyFixed x.address
    let a := copyFixed x.payload.rowGroup
    let b := copyFixed x.payload.colGroup
    let c := copyFixed x.payload.slot
    let p := copyFixed x.payload.page
    let tail := copyBootSeatRows xs
    ⟨⟨k.result,⟨p.result,c.result,a.result,b.result⟩⟩::tail.result,
      k.steps+a.steps+b.steps+c.steps+p.steps+tail.steps+7⟩

theorem copy_boot_seat_rows_exact {w d pg : ℕ} (xs : List (RefRow w (SeatField d pg))) :
    copyBootSeatRows xs=⟨xs,3+(3*w+3*d+3*pg+48)*xs.length⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨k,⟨p,c,a,b⟩⟩
    simp only [copyBootSeatRows,copy_fixed_exact,ih,List.length_cons,Nat.mul_succ]
    congr 1
    omega

/-- Read the single local query referent from the current real port
key. Its returned owner and seat operands are copied explicitly. -/
def readBootQueryRow {w own sw : ℕ} (tape : List (RefRow w (Word own × Word sw × Bool)))
    (address : Word w) : Meter (Word own × Word sw × Bool) :=
  let k := copyFixed address
  let found := locate k.result tape
  let row := found.result.getD (word 0,word 0,false)
  let first := copyFixed row.1
  let seat := copyFixed row.2.1
  ⟨(first.result,seat.result,row.2.2),k.steps+found.steps+first.steps+seat.steps+6⟩

theorem actual_boot_query_row_and_width {w own sw : ℕ}
    (tape : List (RefRow w (Word own × Word sw × Bool))) (k : Word w)
    (fields : Word own × Word sw × Bool)
    (hit : (locate k tape).result=some fields) :
    (readBootQueryRow tape k).result=fields ∧
      (readBootQueryRow tape k).steps≤locateFee w tape.length+3*w+3*own+3*sw+9 := by
  have fee := locate_bound k tape
  rcases fields with ⟨x,y,b⟩
  unfold readBootQueryRow
  simp only [copy_fixed_exact,hit,Option.getD_some]
  exact ⟨True.intro,by omega⟩

/-- Reading one actual already resident position-coded descriptor is
a handle selection, not materializing all its raw addressed payloads. -/
def readBootReference {A : Type*} {w : ℕ} (tape : List (RefRow w A)) (address : Word w) :
    Meter (Option A) :=
  let k := copyFixed address
  let r := locate k.result tape
  ⟨r.result,k.steps+r.steps+4⟩

theorem metered_boot_reference_from_existing_register {A : Type*} {w : ℕ}
    (tape : List (RefRow w A)) (address : Word w) :
    (readBootReference tape address).result=(locate address tape).result ∧
      (readBootReference tape address).steps≤locateFee w tape.length+3*w+5 := by
  have fee := locate_bound address tape
  unfold readBootReference
  simp only [copy_fixed_exact]
  exact ⟨True.intro,by omega⟩

#print axioms copy_boot_headers_exact
#print axioms copy_boot_seat_rows_exact
#print axioms actual_boot_query_row_and_width
#print axioms metered_boot_reference_from_existing_register
end J6R58BootScope
