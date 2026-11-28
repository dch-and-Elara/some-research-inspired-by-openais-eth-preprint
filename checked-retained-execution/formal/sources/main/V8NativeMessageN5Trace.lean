import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

/-! N5's delivery contract, with actual event receipts and independently
specified expected payloads. Event costs count work units, not rank;
repeated delivery (including reads from a cache) is legal. -/
namespace V8NativeMessage.N5
open scoped Classical BigOperators

structure Event (Label Value : Type*) (width : ℕ) where
  work : ℕ
  positive : 0<work
  delivered : List (Label×Value)
  cap : delivered.length≤width*work

abbrev Trace (Label Value : Type*) (width : ℕ) := List (Event Label Value width)

variable {L V : Type*} {w : ℕ}

def time (t : Trace L V w) : ℕ := (t.map Event.work).sum

def tape (t : Trace L V w) : List (L×V) := t.flatMap Event.delivered

def Provides (t : Trace L V w) (l : L) (v : V) : Prop := (l,v)∈tape t

theorem provides_iff_event (t : Trace L V w) (l : L) (v : V) :
    Provides t l v ↔ ∃ e∈t, (l,v)∈e.delivered :=
  List.mem_flatMap

@[simp] theorem time_nil : time ([] : Trace L V w)=0 := rfl

@[simp] theorem time_cons (head : Event L V w) (tail : Trace L V w) :
    time (head::tail)=head.work+time tail := rfl

theorem tape_length (t : Trace L V w) : (tape t).length≤w*time t := by
  induction t with
  | nil => simp [tape]
  | cons head tail ih =>
    simp only [tape,List.flatMap_cons,List.length_append,time_cons]
    rw [Nat.mul_add]
    exact Nat.add_le_add head.cap ih

noncomputable def deliveredLabels (t : Trace L V w) : Finset L := (tape t |>.map Prod.fst).toFinset

theorem labels_le_work (t : Trace L V w) : (deliveredLabels t).card≤w*time t := by
  apply le_trans (List.toFinset_card_le (List.map Prod.fst (tape t)))
  rw [List.length_map]
  exact tape_length t

theorem provides_mem (t : Trace L V w) {l : L} {v : V} (h : Provides t l v) :
    l∈deliveredLabels t := by
  rw [deliveredLabels,List.mem_toFinset]
  exact List.mem_map.mpr ⟨(l,v),h,rfl⟩

/-- Only require injectivity within each counted designation class.
A receipt can serve several classes at once. -/
theorem designated_le_work {I : Type*} [Fintype I]
    (t : Trace L V w) (label : I→L) (hLabel : Function.Injective label) (payload : I→V)
    (covers : ∀ i, Provides t (label i) (payload i)) :
    Fintype.card I≤w*time t := by
  calc
    Fintype.card I = (Finset.univ.map ⟨label,hLabel⟩).card := by simp
    _ ≤ (deliveredLabels t).card := by
      apply Finset.card_le_card
      intro l hl
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hl
      exact provides_mem t (covers i)
    _ ≤ _ := labels_le_work t

#print axioms provides_iff_event
#print axioms tape_length
#print axioms labels_le_work
#print axioms designated_le_work
end V8NativeMessage.N5