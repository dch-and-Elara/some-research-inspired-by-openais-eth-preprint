import J6R26DescriptorTreeNative
import J6R51DispatchLegacy
import Mathlib.Data.List.NodupEquivFin

/-! The archival ordinal is genuine data. A complete, repetition-free
CentreDesc menu does not fix its order. One can put either selected
mode first without changing its physical roster or sample masks.
This is an ABI counterexample, not a claim about every deployed order. -/
namespace J6R58OrdinalSpace
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion J6R51Dispatch

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 25500000
set_option maxRecDepth 4400
set_option maxSynthPendingDepth 12
set_option Elab.async false

section Order
variable {A : Type*} [DecidableEq A]

def promote (chosen : A) (order : List A) : List A :=
  chosen::order.filter (fun x=>decide (x≠chosen))

theorem promoted_order_is_unique {l : List A} (nodup : l.Nodup) (chosen : A) :
    (promote chosen l).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨?_,nodup.filter _⟩
  simp

theorem promoted_order_remains_complete {l : List A} (all : ∀ a,a∈l) (chosen x : A) :
    x∈promote chosen l := by
  unfold promote
  by_cases eq : x=chosen
  · exact List.mem_cons.mpr (Or.inl eq)
  · exact List.mem_cons.mpr (Or.inr (List.mem_filter.mpr ⟨all x,decide_eq_true eq⟩))
end Order

noncomputable section

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "M" => (NativeMenu (N sel) v.parent v.centerAt)

def promoteActualCentre (chosen : M) : Prepared cfg sel r hf := by
  classical
  refine {T with active:=?_}
  intro c hc ha
  by_cases sameCall : c=v.parent
  · subst c
    let old := T.active v.parent hc ha
    refine {old with tape:=?_}
    intro t
    by_cases sameCentre : t=v.centerAt
    · subst t
      let current := old.tape v.centerAt
      exact
        { current with
          modes := promote chosen current.modes
          modeUnique := promoted_order_is_unique current.modeUnique chosen
          modeComplete := promoted_order_remains_complete current.modeComplete chosen }
    · exact old.tape t
  · exact T.active c hc ha

theorem original_centre_new_order_and_unchanged_physical_data (chosen : M) :
    let old := (ticketActive T v).tape v.centerAt
    let got := (ticketActive (promoteActualCentre T v chosen) v).tape v.centerAt
    got.modes=promote chosen old.modes ∧
    got.roster=old.roster ∧ HEq got.masks old.masks := by
  classical
  simp [promoteActualCentre, ticketActive]

/-! The archival index uses the same lawful equality as the proof. -/
theorem actual_mode_ordinal_is_index :
    modeOrdinal T v=((ticketActive T v).tape v.centerAt).modes.idxOf v.modeAt := by
  classical
  unfold modeOrdinal
  apply same_index_for_lawful_comparators <;> infer_instance

theorem actual_legacy_rank_not_determined_by_roster_and_ready (other : M)
    (distinct : other≠v.modeAt) :
    let A := promoteActualCentre T v v.modeAt
    let B := promoteActualCentre T v other
    A.bank=T.bank ∧ B.bank=T.bank ∧
    ((ticketActive A v).tape v.centerAt).roster=((ticketActive B v).tape v.centerAt).roster ∧
    HEq ((ticketActive A v).tape v.centerAt).masks ((ticketActive B v).tape v.centerAt).masks ∧
    modeOrdinal A v=0 ∧ modeOrdinal B v≠0 := by
  classical
  let A := promoteActualCentre T v v.modeAt
  let B := promoteActualCentre T v other
  have a := original_centre_new_order_and_unchanged_physical_data T v v.modeAt
  have b := original_centre_new_order_and_unchanged_physical_data T v other
  dsimp only at a b
  refine ⟨rfl,rfl,a.2.1.trans b.2.1.symm,a.2.2.trans b.2.2.symm,?_,?_⟩
  · rw [actual_mode_ordinal_is_index]
    change ((ticketActive A v).tape v.centerAt).modes.idxOf v.modeAt=0
    rw [a.1]
    simp [promote]
  · rw [actual_mode_ordinal_is_index]
    change ((ticketActive B v).tape v.centerAt).modes.idxOf v.modeAt≠0
    rw [b.1]
    have off : (other == v.modeAt)=false := Bool.eq_false_iff.mpr
      (fun eq=>distinct (beq_iff_eq.mp eq))
    simp [promote,List.idxOf_cons,off]

#print axioms promoted_order_is_unique
#print axioms promoted_order_remains_complete
#print axioms original_centre_new_order_and_unchanged_physical_data
#print axioms actual_mode_ordinal_is_index
#print axioms actual_legacy_rank_not_determined_by_roster_and_ready
end
end J6R58OrdinalSpace
