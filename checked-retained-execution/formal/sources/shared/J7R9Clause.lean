import J6Guard
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Nodup

/-!
# Raw CNF preprocessing for the source clause network

Use Lean's actual list-based Std.Sat.CNF, preserve the declared variable
type, retain empty clauses, discard only syntactic tautologies, and
emit exactly one port per distinct variable in a surviving clause.
-/

open Std.Sat
open scoped BigOperators

namespace J7R9Clause
variable {V : Type*} [DecidableEq V]

def taut (c : CNF.Clause V) : Bool :=
  c.any (fun l => decide ((l.1,!l.2) ∈ c))

theorem taut_true (c : CNF.Clause V) : taut c=true ↔
    ∃ l ∈ c, (l.1,!l.2) ∈ c := by
  simp [taut, List.any_eq_true]

omit [DecidableEq V] in
theorem eval_true (x : V → Bool) (c : CNF.Clause V) :
    c.eval x=true ↔ ∃ l ∈ c, x l.1=l.2 := by
  simp [CNF.Clause.eval,List.any_eq_true]

theorem taut_satisfied (c : CNF.Clause V) (h : taut c=true) (x : V → Bool) :
    c.eval x=true := by
  obtain ⟨⟨v,b⟩,hb,hnot⟩ := (taut_true c).mp h
  apply (eval_true x c).mpr
  by_cases he : x v=b
  · exact ⟨(v,b),hb,he⟩
  · refine ⟨(v,!b),hnot,?_⟩
    cases b <;> cases hv : x v <;> simp_all

theorem dedup_eval (c : CNF.Clause V) (x : V → Bool) :
    CNF.Clause.eval x c.dedup=c.eval x := by
  apply Bool.eq_iff_iff.mpr
  simp [eval_true]

def clean : CNF V → CNF V
  | [] => []
  | c::F => if taut c then clean F else c.dedup::clean F

theorem clean_eval (F : CNF V) (x : V → Bool) : (clean F).eval x=F.eval x := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    cases h : taut c
    · simp [clean,h,ih,dedup_eval]
    · simp [clean,h,ih,taut_satisfied c h x]

theorem clean_mem {F : CNF V} {d : CNF.Clause V} (hd : d ∈ clean F) :
    ∃ c ∈ F, taut c=false ∧ d=c.dedup := by
  induction F with
  | nil => simp [clean] at hd
  | cons c F ih =>
    cases h : taut c
    · simp only [clean,h,Bool.false_eq_true,if_false,List.mem_cons] at hd
      rcases hd with rfl|hd
      · exact ⟨c,List.mem_cons_self,h,rfl⟩
      · obtain ⟨u,hu,ht,he⟩ := ih hd
        exact ⟨u,List.mem_cons_of_mem _ hu,ht,he⟩
    · have hd' : d ∈ clean F := by simpa [clean,h] using hd
      obtain ⟨u,hu,ht,he⟩ := ih hd'
      exact ⟨u,List.mem_cons_of_mem _ hu,ht,he⟩

theorem clean_no_repeat {F : CNF V} {d : CNF.Clause V} (hd : d ∈ clean F) :
    (d.map Prod.fst).Nodup := by
  obtain ⟨c,_hc,ht,rfl⟩ := clean_mem hd
  apply (List.nodup_dedup c).map_on
  intro a ha b hb he
  rcases a with ⟨v,s⟩
  rcases b with ⟨w,t⟩
  dsimp only at he
  subst w
  by_contra hn
  have hs : s≠t := fun hh => hn (by rw [hh])
  have hneg : t=(!s) := by cases s <;> cases t <;> simp_all
  have ht' := (taut_true c).mpr ⟨(v,s),List.mem_dedup.mp ha,
    by simpa [← hneg] using (List.mem_dedup.mp hb)⟩
  simp [ht] at ht'

theorem clean_width {F : CNF V} (k : ℕ) (h : ∀ c ∈ F, c.length≤k) :
    ∀ d ∈ clean F, d.length≤k := by
  intro d hd
  obtain ⟨c,hc,_ht,rfl⟩ := clean_mem hd
  exact (List.dedup_sublist c).length_le.trans (h c hc)

variable [Fintype V]

/-- Includes all original declared variables, even if their only
occurrences were in clauses removed as tautologies. -/
theorem clean_count (F : CNF V) : PinnedCNF.modelCount (clean F)=PinnedCNF.modelCount F := by
  classical
  unfold PinnedCNF.modelCount
  congr 1
  ext x
  simp [clean_eval]

/-- The printed logical guard applied after cleanup is a literal CNF
with the same +1 count and true all-zero row assignment. -/
theorem guarded_clean_count (F : CNF V) :
    PinnedCNF.modelCount (J6Guard.guardedFormula (clean F))=1+PinnedCNF.modelCount F :=
  (J6Guard.literal_guarded_count (clean F)).trans (congrArg (1+·) (clean_count F))

#print axioms taut_satisfied
#print axioms clean_eval
#print axioms clean_no_repeat
#print axioms clean_width
#print axioms clean_count
#print axioms guarded_clean_count

end J7R9Clause

