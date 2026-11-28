import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-! The actual dense Boolean superset transform for all parity moments. -/
namespace J45Parity

open scoped BigOperators Classical

variable {D R : Type*} [DecidableEq D] [AddCommMonoid R]

/-- Processed directions can be added to S in all combinations. -/
def partialZeta (done : Finset D) (f : Finset D→R) (S : Finset D) : R :=
  ∑ T ∈ (done \ S).powerset, f (S∪T)

def step (j : D) (f : Finset D→R) (S : Finset D) : R :=
  if j∈S then f S else f S + f (insert j S)

theorem step_partial (done : Finset D) (f : Finset D→R) (j : D) (h : j∉done) :
    step j (partialZeta done f) = partialZeta (insert j done) f := by
  funext S
  by_cases hj : j∈S
  · rw [step,if_pos hj]
    have hh : insert j done \ S = done \ S := by
      ext d
      by_cases hd : d=j
      · subst d; simp [hj]
      · simp [hd]
    simp [partialZeta,hh]
  · rw [step,if_neg hj]
    have hk : insert j done \ S = insert j (done \ S) := by ext d; simp; aesop
    have he : done \ insert j S = done \ S := by
      ext d
      by_cases hd : d=j
      · subst d; simp [h]
      · simp [hd]
    simp only [partialZeta,hk,he]
    rw [Finset.sum_powerset_insert (fun hmem => h (Finset.mem_sdiff.mp hmem).1)]
    congr 1
    refine Finset.sum_congr rfl fun T _ => ?_
    congr 1
    ext d
    simp

/-- Concrete one-cell update. Its right-hand partner already contains j. -/
def update (j : D) (f : Finset D→R) (S : Finset D) : Finset D→R :=
  Function.update f S (f S + f (insert j S))

theorem active_sweep (j : D) (xs : List (Finset D)) (nd : xs.Nodup)
    (ok : ∀ S∈xs,j∉S) (f : Finset D→R) (S : Finset D) :
    xs.foldl (update j) f S = if S∈xs then f S + f (insert j S) else f S := by
  induction xs generalizing f with
  | nil => simp
  | cons T xs ih =>
    rw [List.nodup_cons] at nd
    rw [List.foldl_cons,ih nd.2 (fun U hU => ok U (List.mem_cons_of_mem _ hU))]
    have hn : insert j S ≠ T := by
      intro he
      exact ok T (List.mem_cons_self ..) (he ▸ Finset.mem_insert_self ..)
    by_cases hs : S∈xs
    · have hST : S≠T := fun he => nd.1 (he ▸ hs)
      simp [hs,update, hST,hn]
    · by_cases he : S=T
      · subst S
        simp [hs,update]
      · simp [hs,he,update]

variable [Fintype D]

def active (j : D) : Finset (Finset D) :=
  Finset.univ.filter fun S => j∉S

noncomputable def sweep (j : D) (f : Finset D→R) : Finset D→R :=
  (active j).toList.foldl (update j) f

theorem sweep_eq (j : D) (f : Finset D→R) : sweep j f = step j f := by
  funext S
  rw [sweep,active_sweep j _ (Finset.nodup_toList _) (fun U hU => by
    simpa [active] using hU)]
  by_cases h : j∈S <;> simp [step,active,h]

noncomputable def run (f : Finset D→R) : List D → Finset D→R
  | [] => f
  | j::js => sweep j (run f js)

theorem run_exact (f : Finset D→R) (js : List D) (nd : js.Nodup) :
    run f js = partialZeta js.toFinset f := by
  induction js with
  | nil => ext S; simp [run,partialZeta]
  | cons j js ih =>
    rw [List.nodup_cons] at nd
    rw [run,ih nd.2,sweep_eq,List.toFinset_cons,
      step_partial _ _ _ (by simpa using nd.1)]

theorem all_moments (f : Finset D→R) (S : Finset D) :
    run f (Finset.univ : Finset D).toList S =
      ∑ T : Finset D, if S⊆T then f T else 0 := by
  classical
  rw [run_exact f _ (Finset.nodup_toList _)]
  simp only [Finset.toList_toFinset,partialZeta]
  rw [← Finset.sum_filter]
  have hset : (Finset.univ.filter (fun T : Finset D => S⊆T)) =
      ((Finset.univ \ S).powerset.image (fun T => S∪T)) := by
    ext T
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image,Finset.mem_powerset]
    constructor
    · intro h
      exact ⟨T \ S, (by intro x hx; simp only [Finset.mem_sdiff,Finset.mem_univ,true_and]
                                      ; exact (Finset.mem_sdiff.mp hx).2), Finset.union_sdiff_of_subset h⟩
    · rintro ⟨T,_,rfl⟩
      exact Finset.subset_union_left
  rw [hset, Finset.sum_image]
  intro x hx y hy he
  have hs (v : Finset D) (hv : v ∈ (Finset.univ \ S).powerset) : (S∪v) \ S=v := by
    have h := Finset.mem_powerset.mp hv
    ext d
    simp only [Finset.mem_sdiff,Finset.mem_union]
    have hh : d∈v → d∉S := fun hv => (Finset.mem_sdiff.mp (h hv)).2
    tauto
  have he' := congrArg (fun v : Finset D => v \ S) he
  simpa only [hs x hx,hs y hy] using he'

theorem active_card (j : D) : (active j).card = 2^(Fintype.card D-1) := by
  have h : active j = ((Finset.univ : Finset D).erase j).powerset := by
    ext S
    simp [active,Finset.subset_erase]
  rw [h,Finset.card_powerset,Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ]

/-- One addition, two reads and one write per active pair. No paid
Boolean-query operation is concealed in the initial transform input. -/
theorem sweep_total_additions :
    (∑ j : D,(active j).toList.length) = Fintype.card D*2^(Fintype.card D-1) := by
  simp [active_card]

omit [DecidableEq D] in
/-- Enumerating the active addresses by a dense membership test is charged
as well. Each stage has one test per state. -/
theorem selection_tests :
    Fintype.card (D × Finset D) = Fintype.card D * 2^Fintype.card D := by
  simp

/-- Charge each pair's two reads, write, addition and address handling. -/
theorem sweep_access_tariff (read write add address : ℕ) :
    (∑ j : D,(active j).toList.length*(2*read+write+add+address)) =
      (Fintype.card D*2^(Fintype.card D-1))*(2*read+write+add+address) := by
  rw [← Finset.sum_mul,sweep_total_additions]

#print axioms step_partial
#print axioms active_sweep
#print axioms sweep_eq
#print axioms run_exact
#print axioms all_moments
#print axioms active_card
#print axioms sweep_total_additions
#print axioms selection_tests
#print axioms sweep_access_tariff

end J45Parity