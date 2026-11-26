import P5RootGreedyCollision

namespace Paper5.RootGreedy
open scoped Classical BigOperators
open J6R11Collision J6R11CollisionGreedy GuardExpectation
noncomputable section
variable {E R C A : Type*} [Fintype E] [Fintype R] [Fintype C] [Fintype A] [Nonempty A]
variable (row : E → R) (col : E → C)

omit [Fintype R] [Fintype C] [Nonempty A] in
private theorem weights_congr {s : Finset (R ⊕ C)} {z z' : R ⊕ C → A}
    (agree : ∀ j∈s,z j=z' j) : weights z s = weights z' s := by
  funext j b
  by_cases h : j∈s <;> simp [weights,fixOn,h,fun hj => agree j hj]

omit [Fintype R] [Fintype C] [Nonempty A] in
private theorem prefix_congr {s : Finset (R ⊕ C)} {z : R ⊕ C → A}
    (p : Prefix row col z s) : ∀ z' : R ⊕ C → A, (∀ j∈s,z j=z' j) → Prefix row col z' s := by
  induction p with
  | empty => exact fun _ _ => .empty
  | @step s i _ hi hm ih =>
    intro z' agree
    have a : ∀ j∈s,z j=z' j := fun j h => agree j (Finset.mem_insert_of_mem h)
    have w := weights_congr a
    have e := agree i (Finset.mem_insert_self _ _)
    exact .step (ih z' a) hi (by simpa only [←w,←e] using hm)

omit [Fintype R] [Fintype C] in
theorem minimizing_transcript_exists (s : Finset (R ⊕ C)) :
    ∃ z : R ⊕ C → A, Prefix row col z s := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => Classical.choice inferInstance,.empty⟩
  | @insert i s hi ih =>
    obtain ⟨z,p⟩ := ih
    obtain ⟨b,_,hm⟩ := Finset.exists_min_image Finset.univ
      (fun b : A => compressed row col (fixAt (weights z s) i b)) Finset.univ_nonempty
    let z' := Function.update z i b
    have a : ∀ j∈s,z j=z' j := by
      intro j hj; have h : j≠i := fun he => hi (he ▸ hj)
      simp [z',h]
    refine ⟨z',.step (prefix_congr row col p z' a) hi ?_⟩
    rw [←weights_congr a]
    simpa [z'] using (fun b' : A => hm b' (Finset.mem_univ b'))

#print axioms minimizing_transcript_exists
end
end Paper5.RootGreedy
