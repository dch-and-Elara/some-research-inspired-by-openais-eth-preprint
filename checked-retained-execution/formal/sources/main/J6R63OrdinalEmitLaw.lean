import J6R63OrdinalDrain
import J6R58OrdinalSpaceAlignment

/-! A typed archive can be licensed by exact positions of its true
prefixes, without either computing a lookup or elaborating a global
comparator for the physical mode type here. -/
namespace J6R63Ordinal
open J6R15ModeCost J6R25PreparedSupply J6R58OrdinalSpace
set_option autoImplicit false
set_option maxHeartbeats 5200000

variable {X : Type*} {q n b : ℕ}
variable (encode : X→List ℕ) (ordinal : X→ℕ)

def PrefixNames (order : List X) : Prop :=
  ∀ done x pending,order=done++x::pending → ordinal x=done.length

def AlignedFit (p : Pending q n) (i : Word b) : Prop :=
  ∃ order : List X, order.length<2^b ∧ PrefixNames ordinal order ∧ RankAlignment encode order p i

def LiteralAddress (raw : List (Word q)) (i : Word b) : Prop :=
  ∃ x,raw.map Word.val=encode x ∧ i.val=ordinal x

theorem actual_cursor_supplies_its_prefix_address (pos : 0<b) :
    EmissionLaw (AlignedFit (q:=q) (n:=n) (b:=b) encode ordinal) (LiteralAddress encode ordinal) := by
  constructor
  intro p i raw st event ok
  obtain ⟨order,room, names, seen, tail, whole, atSeen, follows⟩ := ok
  obtain ⟨rest, shape, _, beyond⟩ := p.next_data event follows
  cases tail with
  | nil => simp at shape
  | cons x xs =>
    change encode x::xs.map encode=raw.map Word.val::rest at shape
    have coords :=  List.cons.inj shape
    have nextFits : i.val+1<2^b := by
      rw [atSeen]
      rw [whole,List.length_append,List.length_cons] at room
      omega
    have newOrdinal := (increment_exact pos i nextFits).1
    have enlarged : (increment i).result.val=(seen++[x]).length := by
      rw [newOrdinal,atSeen,List.length_append]
      rfl
    have namesThis := names seen x xs whole
    have whole' : order=(seen++[x])++xs := whole.trans (List.append_assoc seen [x] xs).symm
    have nextTrace : Runs n (p.tail event).state (xs.map encode) (.ascend []) := by
      rw [coords.2]
      exact beyond
    exact ⟨⟨x,coords.1.symm,atSeen.trans namesThis.symm⟩,
      ⟨order,room,names,seen++[x],xs,whole',enlarged,nextTrace⟩⟩

theorem prefix_names_from_a_lawful_archival_index [BEq X] [LawfulBEq X]
    (order : List X) (unique : order.Nodup) (correct : ∀ x,ordinal x=order.idxOf x) :
    PrefixNames ordinal order := by
  intro seen x tail whole
  have all : (x::(seen++tail)).Nodup := List.nodup_middle.mp (whole ▸ unique)
  have fresh : x∉seen := fun h=>(List.nodup_cons.mp all).1 (List.mem_append.mpr (Or.inl h))
  rw [correct,whole,index_of_unseen_head_at_prefix seen tail x fresh]

#print axioms actual_cursor_supplies_its_prefix_address
#print axioms prefix_names_from_a_lawful_archival_index
end J6R63Ordinal
