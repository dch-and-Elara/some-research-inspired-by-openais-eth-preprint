import F5R61ActualCycleLists

namespace F5R61
open F5R60
set_option autoImplicit false

def lastFrom {P : Type} (a : P) : List P → P
  | [] => a
  | b :: rest => lastFrom b rest

theorem lastFrom_mem {P : Type} (a : P) (xs : List P) : lastFrom a xs ∈ a :: xs := by
  induction xs generalizing a with
  | nil => simp [lastFrom]
  | cons b rest ih =>
    exact List.mem_cons_of_mem _ (ih b)

theorem ordered_chain {P : Type} (a : P) (xs : List P) :
    Chain (fun (_ : P) => false) a xs (lastFrom a xs) := by
  induction xs generalizing a with
  | nil => rfl
  | cons b rest ih => exact ⟨id,ih b⟩

variable {V E T : Type} [DecidableEq V] [DecidableEq T]
variable (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)

def firstSlot (n : Logical V T) : PrivatePos V E T :=
  (actualCycleList G v e t n).head (actualCycleList_nonempty G v e t n)

def remainingSlots (n : Logical V T) : List (PrivatePos V E T) :=
  (actualCycleList G v e t n).tail

theorem reconstruct_cycle_list (n : Logical V T) :
    firstSlot G v e t n :: remainingSlots G v e t n = actualCycleList G v e t n :=
  List.cons_head_tail (actualCycleList_nonempty G v e t n)

def generatedPrintedCycles : PrintedCycles G where
  first := firstSlot G v e t
  rest := remainingSlots G v e t
  last n := lastFrom (firstSlot G v e t n) (remainingSlots G v e t n)
  firstName n := (actualCycleList_exact_members G v e t _ n).1
    (List.head_mem (actualCycleList_nonempty G v e t n))
  lastName n := by
    apply (actualCycleList_exact_members G v e t _ n).1
    rw [← reconstruct_cycle_list G v e t n]
    exact lastFrom_mem _ _
  restName n z inTail := (actualCycleList_exact_members G v e t _ n).1
    (List.mem_of_mem_tail inTail)
  covered z := by
    rw [reconstruct_cycle_list]
    exact (actualCycleList_exact_members G v e t _ _).2 rfl
  chainOrder n := ordered_chain _ _

theorem generated_physical_F1_decides_allowed :
    (∃ b d, PhysicalPrinted G (generatedPrintedCycles G v e t) b d) ↔ ∃ x, Allowed G x :=
  actual_F1_sat_iff_allowed G (generatedPrintedCycles G v e t)

#print axioms lastFrom_mem
#print axioms ordered_chain
#print axioms reconstruct_cycle_list
#print axioms generatedPrintedCycles
#print axioms generated_physical_F1_decides_allowed
end F5R61
