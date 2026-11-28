import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

/-! MAIN 1850–1865: the representative pass is a first-witness scan;
the contribution pass is a full scan with a conditional factor call. -/
namespace V8NativeMessage.C3.NativeAssembly.MainScan
open scoped Classical BigOperators
noncomputable section

section Loop
variable {A R : Type*}

def search (p : A→Bool) : List A→Option A
  | [] => none
  | a::as => if p a then some a else search p as

theorem search_some (p : A→Bool) (xs : List A) (a : A)
    (h : search p xs=some a) : a∈xs ∧ p a=true := by
  induction xs with
  | nil => simp [search] at h
  | cons b bs ih =>
    by_cases hb : p b=true
    · have e : b=a := Option.some.inj (by simpa only [search,if_pos hb] using h)
      subst a
      exact ⟨List.mem_cons_self, hb⟩
    · have hx := ih (by simpa only [search,if_neg hb] using h)
      exact ⟨List.mem_cons_of_mem _ hx.1,hx.2⟩

theorem search_exists (p : A→Bool) (xs : List A) :
    (search p xs).isSome = true ↔ ∃ a∈xs, p a=true := by
  induction xs with
  | nil => simp [search]
  | cons b bs ih =>
    by_cases hb : p b=true
    · exact ⟨fun _ => ⟨b,List.mem_cons_self,hb⟩,fun _ => by simp [search,hb]⟩
    · simp only [search,if_neg hb,ih,List.mem_cons]
      constructor
      · rintro ⟨a,ha,hp⟩
        exact ⟨a,Or.inr ha,hp⟩
      · rintro ⟨a,he,hp⟩
        rcases he with rfl | he
        · exact (hb hp).elim
        · exact ⟨a,he,hp⟩

variable [AddCommMonoid R]

/-- Accumulate every event in the supplied scan order, without a
zero-product or empty-target early-exit branch. -/
def fullFold (event : A→R) (xs : List A) : R :=
  xs.foldl (fun a x => a+event x) 0

theorem foldl_accumulate (event : A→R) (xs : List A) (base : R) :
    xs.foldl (fun a x => a+event x) base=base+(xs.map event).sum := by
  induction xs generalizing base with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons,List.map_cons,List.sum_cons,ih,add_assoc]

theorem fullFold_on_finite [Fintype A] (event : A→R) :
    fullFold event (Finset.univ : Finset A).toList=∑ x, event x := by
  unfold fullFold
  rw [foldl_accumulate,zero_add,Finset.sum_map_toList]
end Loop

structure Frame (V G : Type*) [Fintype V] where
  group : V→G
  rows : G→ℕ
  C : ∀ g, Fin (rows g) → {v : V // group v=g} → ℤ
  y : ∀ g, Fin (rows g) → ℤ
  E : Finset V

variable {V G R : Type*} [Fintype V]

abbrev Word (L : Frame V G) (g : G) := {v : V // L.group v=g}→Bool

def measure (L : Frame V G) (g : G) (x : Word L g) (j : Fin (L.rows g)) : ℤ :=
  ∑ v, L.C g j v * (if x v then 1 else 0)

def unrestricted (L : Frame V G) (g : G) (x : Word L g) : Prop :=
  ∀ j, measure L g x j=L.y g j

def eligible (L : Frame V G) (g : G) (x : Word L g) : Prop :=
  unrestricted L g x ∧ ∀ v : {v : V // L.group v=g}, v.val∈L.E → x v=true

def words (L : Frame V G) (g : G) : List (Word L g) := Finset.univ.toList

def representative (L : Frame V G) (g : G) : Option (Word L g) :=
  search (fun x => decide (unrestricted L g x)) (words L g)

theorem representative_exists_iff (L : Frame V G) (g : G) :
    (representative L g).isSome = true ↔ ∃ x, unrestricted L g x := by
  unfold representative words
  rw [search_exists]
  simp

def feasible (L : Frame V G) : Prop := ∀ g, (representative L g).isSome = true

def repWord (L : Frame V G) (h : feasible L) (g : G) : Word L g :=
  (representative L g).get (h g)

theorem repWord_unrestricted (L : Frame V G) (h : feasible L) (g : G) :
    unrestricted L g (repWord L h g) := by
  have hs : representative L g = some (repWord L h g) :=
    (Option.some_get (h g)).symm
  exact of_decide_eq_true ((search_some _ _ _ hs).2)

def merge (L : Frame V G) (rep : ∀ g, Word L g) (g : G) (x : Word L g) : V→Bool :=
  fun v => if h : L.group v=g then x ⟨v,h⟩ else rep (L.group v) ⟨v,rfl⟩

theorem merge_own (L : Frame V G) (rep : ∀ g, Word L g) (g : G)
    (x : Word L g) (v : {v : V // L.group v=g}) : merge L rep g x v.val=x v := by
  simp only [merge,dif_pos v.property]

theorem merge_other (L : Frame V G) (rep : ∀ g, Word L g) (g : G)
    (x : Word L g) (v : V) (h : L.group v≠g) :
    merge L rep g x v=rep (L.group v) ⟨v,rfl⟩ := by simp only [merge,dif_neg h]

abbrev Meter (R : Type*) := ℕ × ℕ × R

variable [AddCommMonoid R]

def entry (L : Frame V G) (A : G→(V→Bool)→R) (h : feasible L)
    (g : G) (x : Word L g) : Meter R :=
  if eligible L g x then (1,1,A g (merge L (repWord L h) g x)) else (1,0,0)

def secondScan (L : Frame V G) (A : G→(V→Bool)→R) (h : feasible L)
    (g : G) : Meter R :=
  fullFold (entry L A h g) (words L g)

theorem second_exact (L : Frame V G) (A : G→(V→Bool)→R) (h : feasible L) (g : G) :
    secondScan L A h g=∑ x : Word L g, entry L A h g x :=
  fullFold_on_finite _

theorem second_tests_every_word (L : Frame V G) (A : G→(V→Bool)→R) (h : feasible L) (g : G) :
    (secondScan L A h g).1=2^Fintype.card {v : V // L.group v=g} := by
  rw [second_exact]
  change (AddMonoidHom.fst ℕ (ℕ×R)) (∑ x : Word L g, entry L A h g x)=_
  rw [map_sum]
  change (∑ x : Word L g, (entry L A h g x).1)=_
  have hg (x : Word L g) : (entry L A h g x).1=1 := by
    by_cases hx : eligible L g x <;> simp [entry,hx]
  simp [hg]

theorem second_value_is_actual_fibre (L : Frame V G) (A : G→(V→Bool)→R)
    (h : feasible L) (g : G) :
    (secondScan L A h g).2.2 =
      ∑ x ∈ (Finset.univ : Finset (Word L g)).filter (eligible L g),
        A g (merge L (repWord L h) g x) := by
  rw [second_exact]
  change ((AddMonoidHom.snd ℕ R).comp (AddMonoidHom.snd ℕ (ℕ×R)))
    (∑ x : Word L g, entry L A h g x) = _
  rw [map_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : eligible L g x <;> simp [entry,hx]

theorem second_factor_calls (L : Frame V G) (A : G→(V→Bool)→R)
    (h : feasible L) (g : G) :
    (secondScan L A h g).2.1 =
      ((Finset.univ : Finset (Word L g)).filter (eligible L g)).card := by
  rw [second_exact]
  change ((AddMonoidHom.fst ℕ R).comp (AddMonoidHom.snd ℕ (ℕ×R)))
    (∑ x : Word L g,entry L A h g x)=_
  have hs : (∑ x ∈ (Finset.univ : Finset (Word L g)).filter (eligible L g), (1:ℕ)) =
      ((Finset.univ : Finset (Word L g)).filter (eligible L g)).card := by simp
  rw [map_sum,←hs,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : eligible L g x <;> simp [entry,hx]

#print axioms second_factor_calls
#print axioms search_some
#print axioms search_exists
#print axioms fullFold_on_finite
#print axioms representative_exists_iff
#print axioms repWord_unrestricted
#print axioms merge_own
#print axioms merge_other
#print axioms second_tests_every_word
#print axioms second_value_is_actual_fibre
end
end V8NativeMessage.C3.NativeAssembly.MainScan
