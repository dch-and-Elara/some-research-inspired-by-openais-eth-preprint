import F5R60PhysicalF1
import F5R61CyclePositions
import Mathlib.Tactic.FinCases

/-! Compiles the forbidden pairs and the other positions directly from the
physical F1 slots. The two originals with a repeated vertex name are the
oriented edge request and the final triple clause; the switch repeats its
own vertex as well. The occurrence tags themselves are never identified. -/
namespace F5R61
open F5R60
set_option autoImplicit false
set_option linter.unusedSimpArgs false

structure Listing (A : Type) where
  elems : List A
  once : elems.Nodup
  all : ∀ a, a ∈ elems

variable {V E T : Type}

def switches (L : Listing V) : List (PrivatePos V E T × PrivatePos V E T) :=
  L.elems.map (fun v => (.sw v 0, .sw v 1))

def directedRequests (L : Listing E) : List (PrivatePos V E T × PrivatePos V E T) :=
  L.elems.map (fun e => (.er e 0, .er e 2))

def tripleRequests (L : Listing T) : List (PrivatePos V E T × PrivatePos V E T) :=
  L.elems.map (fun t => (.tr t 8, .tr t 9))

def allForbidden (v : Listing V) (e : Listing E) (d : Listing T) :
    List (PrivatePos V E T × PrivatePos V E T) :=
  switches v ++ directedRequests e ++ tripleRequests d

def edgeSingles (e : E) : List (PrivatePos V E T) := [.cf e 0, .cf e 1, .er e 1]

def tripleSingles (t : T) : List (PrivatePos V E T) :=
  [.tr t 0,.tr t 1,.tr t 2,.tr t 3,.tr t 4,.tr t 5,.tr t 6,.tr t 7]

def allSingles (e : Listing E) (t : Listing T) : List (PrivatePos V E T) :=
  e.elems.flatMap edgeSingles ++ t.elems.flatMap tripleSingles

theorem each_pair_has_same_logical_name (G : RequestGraph V E T)
    (v : Listing V) (e : Listing E) (t : Listing T) (p : PrivatePos V E T × PrivatePos V E T)
    (mem : p ∈ allForbidden v e t) : nameOf G p.1 = nameOf G p.2 := by
  simp only [allForbidden,List.mem_append,switches,directedRequests,tripleRequests,List.mem_map] at mem
  rcases mem with (⟨a,_,rfl⟩|⟨a,_,rfl⟩)|⟨a,_,rfl⟩ <;> rfl

theorem every_source_slot_listed (v : Listing V) (e : Listing E) (t : Listing T)
    (p : PrivatePos V E T) :
    p ∈ (allForbidden v e t).map Prod.fst ∨
    p ∈ (allForbidden v e t).map Prod.snd ∨ p ∈ allSingles e t := by
  have hs (x : V) : (PrivatePos.sw (E:=E) (T:=T) x 0, PrivatePos.sw x 1) ∈ allForbidden v e t := by
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨x,v.all x,rfl⟩))
  have he (x : E) : (PrivatePos.er (V:=V) (T:=T) x 0, PrivatePos.er x 2) ∈ allForbidden v e t := by
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨x,e.all x,rfl⟩))
  have ht (x : T) : (PrivatePos.tr (V:=V) (E:=E) x 8, PrivatePos.tr x 9) ∈ allForbidden v e t :=
    List.mem_append_right _ (List.mem_map.mpr ⟨x,t.all x,rfl⟩)
  have es (x : E) (p : PrivatePos V E T) (m : p ∈ edgeSingles x) : p ∈ allSingles e t :=
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨x,e.all x,m⟩)
  have ts (x : T) (p : PrivatePos V E T) (m : p ∈ tripleSingles x) : p ∈ allSingles e t :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨x,t.all x,m⟩)
  cases p with
  | sw x i =>
    fin_cases i
    · exact Or.inl (List.mem_map.mpr ⟨_,hs x,rfl⟩)
    · exact Or.inr (Or.inl (List.mem_map.mpr ⟨_,hs x,rfl⟩))
  | cf x i =>
    fin_cases i <;> exact Or.inr (Or.inr (es x _ (by simp [edgeSingles])))
  | er x i =>
    fin_cases i
    · exact Or.inl (List.mem_map.mpr ⟨_,he x,rfl⟩)
    · exact Or.inr (Or.inr (es x _ (by simp [edgeSingles])))
    · exact Or.inr (Or.inl (List.mem_map.mpr ⟨_,he x,rfl⟩))
  | tr x i =>
    fin_cases i
    · exact Or.inr (Or.inr (ts x _ (by simp [tripleSingles])))
    · exact Or.inr (Or.inr (ts x _ (by simp [tripleSingles])))
    · exact Or.inr (Or.inr (ts x _ (by simp [tripleSingles])))
    · exact Or.inr (Or.inr (ts x _ (by simp [tripleSingles])))
    · exact Or.inr (Or.inr (ts x _ (by simp [tripleSingles])))
    · exact Or.inr (Or.inr (ts x _ (by simp [tripleSingles])))
    · exact Or.inr (Or.inr (ts x _ (by simp [tripleSingles])))
    · exact Or.inr (Or.inr (ts x _ (by simp [tripleSingles])))
    · exact Or.inl (List.mem_map.mpr ⟨_,ht x,rfl⟩)
    · exact Or.inr (Or.inl (List.mem_map.mpr ⟨_,ht x,rfl⟩))

section Fibres
variable [DecidableEq V] [DecidableEq T]
variable (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)

def pairsOf (n : Logical V T) : List (PrivatePos V E T × PrivatePos V E T) :=
  (allForbidden v e t).filter (fun p => decide (nameOf G p.1 = n))

def singlesOf (n : Logical V T) : List (PrivatePos V E T) :=
  (allSingles (V:=V) e t).filter (fun p => decide (nameOf G p = n))

def actualCycleList (n : Logical V T) : List (PrivatePos V E T) :=
  orderedSlots (pairsOf G v e t n) (singlesOf G e t n)

theorem actualCycleList_exact_members (p : PrivatePos V E T) (n : Logical V T) :
    p ∈ actualCycleList G v e t n ↔ nameOf G p = n := by
  rw [actualCycleList,preserves_all_original_slots]
  constructor
  · rintro (yes|yes|yes)
    · obtain ⟨a,ma,rfl⟩ := List.mem_map.mp yes
      simpa using (List.mem_filter.mp ma).2
    · obtain ⟨a,ma,rfl⟩ := List.mem_map.mp yes
      have e := each_pair_has_same_logical_name G v e t a (List.mem_filter.mp ma).1
      rw [← e]
      simpa using (List.mem_filter.mp ma).2
    · simpa using (List.mem_filter.mp yes).2
  · intro eq
    rcases every_source_slot_listed v e t p with yes|yes|yes
    · obtain ⟨a,ma,rfl⟩ := List.mem_map.mp yes
      exact Or.inl (List.mem_map.mpr ⟨a,List.mem_filter.mpr ⟨ma,by simpa⟩,rfl⟩)
    · obtain ⟨a,ma,rfl⟩ := List.mem_map.mp yes
      have h := (each_pair_has_same_logical_name G v e t a ma).trans eq
      exact Or.inr (Or.inl (List.mem_map.mpr ⟨a,List.mem_filter.mpr ⟨ma,by simpa⟩,rfl⟩))
    · exact Or.inr (Or.inr (List.mem_filter.mpr ⟨yes,by simpa⟩))

theorem actualCycleList_nonempty (n : Logical V T) : actualCycleList G v e t n ≠ [] := by
  intro empty
  cases n with
  | inl x =>
    have present : PrivatePos.sw x 0 ∈ actualCycleList G v e t (.inl x) :=
      (actualCycleList_exact_members G v e t _ _).2 rfl
    rw [empty] at present
    simp at present
  | inr x =>
    have present : PrivatePos.tr x 1 ∈ actualCycleList G v e t (.inr x) :=
      (actualCycleList_exact_members G v e t _ _).2 rfl
    rw [empty] at present
    simp at present
end Fibres

#print axioms each_pair_has_same_logical_name
#print axioms every_source_slot_listed
#print axioms actualCycleList_exact_members
#print axioms actualCycleList_nonempty
end F5R61

