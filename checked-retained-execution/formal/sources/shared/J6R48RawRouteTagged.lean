import J6R48RawRouteWriter
import J6R21AncestorRegistry

/-! A separately charged order adaptor when the resident exporter kept
its actual per-edge keys. A cell-sorted tape is not treated as already
in the native child occurrence order. -/
namespace J6R48RawRoute
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
set_option Elab.async false

def copySeat {a k : ℕ} (s : SeatField a k) : Meter (SeatField a k) :=
  let p := copyFixed s.page
  let j := copyFixed s.slot
  let r := copyFixed s.rowGroup
  let c := copyFixed s.colGroup
  ⟨⟨p.result,j.result,r.result,c.result⟩,p.steps+j.steps+r.steps+c.steps+6⟩

theorem copied_seat_exact {a k : ℕ} (s : SeatField a k) :
    copySeat s=⟨s,3*(a+k)+46⟩ := by
  cases s
  simp only [copySeat,copy_fixed_exact]
  congr 1
  omega

def restoreSeats {w a k : ℕ} (bank : List (RefRow w (SeatField a k))) :
    List (Word w) → Meter (Option (List (SeatField a k)))
  | [] => ⟨some [],4⟩
  | key::keys =>
    let found := locate key bank
    match found.result with
    | none=>⟨none,found.steps+3⟩
    | some seat =>
      let row := copySeat seat
      let tail := restoreSeats bank keys
      ⟨tail.result.map (row.result::·),found.steps+row.steps+tail.steps+8⟩

theorem restore_order_exact {E : Type*} {w a k : ℕ}
    (wanted placed : List E) (key : E→Word w) (seat : E→SeatField a k)
    (unique : Function.Injective key) (covers : ∀ e∈wanted,e∈placed) :
    let bank := placed.map (fun e=>(⟨key e,seat e⟩ : RefRow w (SeatField a k)))
    let out := restoreSeats bank (wanted.map key)
    out.result=some (wanted.map seat) ∧
      out.steps≤4+wanted.length*(locateFee w placed.length+3*(a+k)+54) := by
  let bank := placed.map (fun e=>(⟨key e,seat e⟩ : RefRow w (SeatField a k)))
  have trueRead (e : E) (h : e∈placed) : (locate (key e) bank).result=some (seat e) := by
    apply locate_hit
    · exact List.mem_map.mpr ⟨e,h,rfl⟩
    · intro row inBank eq
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp inBank
      exact congrArg seat (unique eq)
  have cost (e : E) :
      (locate (key e) bank).steps≤locateFee w placed.length := by
    exact (locate_bound _ _).trans_eq (by simp [bank])
  change (restoreSeats bank (wanted.map key)).result=some (wanted.map seat) ∧
    (restoreSeats bank (wanted.map key)).steps≤_
  induction wanted with
  | nil => exact ⟨rfl,by simp [restoreSeats]⟩
  | cons e es ih =>
    obtain ⟨xs,fee⟩ := ih (fun j hj=>covers j (List.mem_cons_of_mem e hj))
    rw [List.map_cons,restoreSeats,trueRead e (covers e List.mem_cons_self)]
    simp only [copied_seat_exact,xs,Option.map_some,List.map_cons,List.length_cons,
      Nat.add_mul,Nat.one_mul,true_and]
    have f := cost e
    omega

#print axioms copied_seat_exact
#print axioms restore_order_exact
end J6R48RawRoute

