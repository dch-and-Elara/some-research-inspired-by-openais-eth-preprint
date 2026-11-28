import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4600000

/-! Mathematical index law for a literal supplied row encoding. This
does not enumerate the logical catalogue in an executed pathway. -/
namespace J6R51Dispatch
open scoped Classical

theorem idx_of_injected_rows {X Y : Type*} (enc : X → Y) (h : Function.Injective enc)
    (mode : X) (order : List X) :
    (order.map enc).idxOf (enc mode)=order.idxOf mode := by
  induction order with
  | nil => rfl
  | cons x xs ih =>
    by_cases e : x=mode
    · subst x
      simp
    · have ne : enc x≠enc mode := fun k=>e (h k)
      simp [e,ne,ih]

#print axioms idx_of_injected_rows
end J6R51Dispatch

