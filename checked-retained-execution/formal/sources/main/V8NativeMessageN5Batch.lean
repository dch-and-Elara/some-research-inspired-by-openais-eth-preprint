import V8NativeMessageN5Trace

set_option autoImplicit false
set_option warningAsError true

/-! An operational instance of the N5 fee contract. A primitive
batch tick has w concrete output slots. Empty slots and duplicate
(cache) deliveries are permitted. This does not identify a bit
instruction of unrestricted native arithmetic with a batch tick. -/
namespace V8NativeMessage.N5
open scoped Classical

variable {L V : Type*} {w : ℕ}

abbrev Tick (L V : Type*) (w : ℕ) := Fin w→Option (L×V)

def Tick.receipts (f : Tick L V w) : List (L×V) := (List.ofFn f).filterMap id

def Tick.event (f : Tick L V w) : Event L V w where
  work := 1
  positive := Nat.one_pos
  delivered := f.receipts
  cap := by
    rw [Nat.mul_one]
    exact (List.length_filterMap_le _ _).trans (by simp)

def realTicks (run : List (Tick L V w)) : Trace L V w := run.map Tick.event

theorem tick_fee (run : List (Tick L V w)) : time (realTicks run)=run.length := by
  induction run with
  | nil => rfl
  | cons f t ih =>
    rw [realTicks,List.map_cons,time_cons,Tick.event,List.length_cons,←ih]
    exact Nat.add_comm 1 _

theorem tick_delivery (f : Tick L V w) (l : L) (v : V) :
    (l,v)∈f.receipts ↔ ∃ j,f j=some (l,v) := by
  simp only [Tick.receipts,List.mem_filterMap,List.mem_ofFn,id_eq]
  constructor
  · rintro ⟨_,⟨j,rfl⟩,h⟩
    exact ⟨j,h⟩
  · rintro ⟨j,h⟩
    exact ⟨f j,⟨j,rfl⟩,h⟩

theorem real_ticks_delivery (run : List (Tick L V w)) (l : L) (v : V) :
    Provides (realTicks run) l v ↔ ∃ f∈run,∃ j,f j=some (l,v) := by
  rw [provides_iff_event]
  constructor
  · rintro ⟨e,he,h⟩
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    exact ⟨f,hf,(tick_delivery f l v).1 h⟩
  · rintro ⟨f,hf,h⟩
    exact ⟨f.event,List.mem_map.mpr ⟨f,hf,rfl⟩,(tick_delivery f l v).2 h⟩

#print axioms tick_fee
#print axioms tick_delivery
#print axioms real_ticks_delivery
end V8NativeMessage.N5