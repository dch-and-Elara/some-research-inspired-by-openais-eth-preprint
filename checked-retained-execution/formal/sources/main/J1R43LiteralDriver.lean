import GuardExpectation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
set_option linter.unusedSectionVars false

/-! An explicit deterministic traversal of the original primitive keys.
Each candidate uses only an independently supplied, proved-correct compact
conditional objective. No full assignment is inspected by the driver. -/
namespace J1R43Literal
open scoped BigOperators
open GuardExpectation

section Minimum
variable {A : Type*}

def better (f : A → ℚ) (best a : A) : A :=
  if f a < f best then a else best

theorem better_le_left (f : A → ℚ) (best a : A) : f (better f best a) ≤ f best := by
  unfold better
  split
  · exact le_of_lt (by assumption)
  · exact le_rfl

theorem better_le_right (f : A → ℚ) (best a : A) : f (better f best a) ≤ f a := by
  unfold better
  split
  · exact le_rfl
  · exact le_of_not_gt (by assumption)

/-- Left-to-right minimum, with ties settled by the earlier candidate. -/
def choose (f : A → ℚ) : List A → A → A
  | [], best => best
  | a::as, best => choose f as (better f best a)

theorem choose_le_initial (f : A → ℚ) (as : List A) (a : A) :
    f (choose f as a) ≤ f a := by
  induction as generalizing a with
  | nil => exact le_rfl
  | cons u us ih =>
    exact (ih (better f a u)).trans (better_le_left f a u)

theorem choose_le_candidate (f : A → ℚ) (as : List A) (best a : A) (ha : a ∈ as) :
    f (choose f as best) ≤ f a := by
  induction as generalizing best with
  | nil => simp at ha
  | cons u us ih =>
    rw [List.mem_cons] at ha
    cases ha with
    | inl h =>
      subst a
      exact (choose_le_initial f us (better f best u)).trans (better_le_right f best u)
    | inr h =>
      exact ih (better f best u) h

end Minimum

section Driver
variable {P A : Type*} [DecidableEq P] [DecidableEq A]

abbrev Marginals (P A : Type*) := P → A → ℚ

/-- The step count here is the explicit number of evaluations of the compact
objective: two on every comparison. It does not count evaluation internals. -/
def chooseLayout (score : Marginals P A → ℚ) (alphabet : List A) (default : A) :
    List P → Marginals P A → (P → A) × ℕ
  | [], _ => ⟨fun _ => default,0⟩
  | k::ks, w =>
    let a := choose (fun a => score (fixAt w k a)) alphabet default
    let tail := chooseLayout score alphabet default ks (fixAt w k a)
    ⟨Function.update tail.1 k a, tail.2 + 2*alphabet.length⟩

theorem chooseLayout_calls (score : Marginals P A → ℚ) (alphabet : List A) (default : A)
    (ks : List P) (w : Marginals P A) :
    (chooseLayout score alphabet default ks w).2 = 2*ks.length*alphabet.length := by
  induction ks generalizing w with
  | nil => simp [chooseLayout]
  | cons k ks ih =>
    simp only [chooseLayout,ih,List.length_cons]
    ring

variable [Fintype P] [Fintype A]

theorem chooseLayout_prefix (score : Marginals P A → ℚ)
    (alphabet : List A) (default : A) (hall : ∀ a : A, a ∈ alphabet)
    (f : (P → A) → ℚ)
    (hscore : ∀ w : Marginals P A, (∀ i, ∑ a, w i a=1) → score w = average w f)
    (ks : List P) (hk : ks.Nodup) (w : Marginals P A)
    (h0 : ∀ i a, 0 ≤ w i a) (h1 : ∀ i, ∑ a, w i a=1) :
    average (fixOn w ks.toFinset (chooseLayout score alphabet default ks w).1) f ≤ average w f := by
  induction ks generalizing w with
  | nil =>
    have hfix : fixOn w ([] : List P).toFinset (fun _=>default) = w := by
      funext i a
      simp [fixOn]
    rw [chooseLayout,hfix]
  | cons k ks ih =>
    let a := choose (fun b => score (fixAt w k b)) alphabet default
    have hN : k ∉ ks := (List.nodup_cons.mp hk).1
    have hN' : k ∉ ks.toFinset := by simpa only [List.mem_toFinset] using hN
    have hkeep : ∀ i, ∑ b, fixAt w k a i b=1 := fixAt_normalized w h1 k a
    obtain ⟨b,hb⟩ := exists_decreasing_fixAt w h0 h1 f k
    have hb' : score (fixAt w k a) ≤ score (fixAt w k b) :=
      choose_le_candidate (fun b => score (fixAt w k b)) alphabet default b (hall b)
    rw [hscore _ hkeep,hscore _ (fixAt_normalized w h1 k b)] at hb'
    have htail := ih (List.nodup_cons.mp hk).2 (fixAt w k a) (fixAt_nonneg w h0 k a) hkeep
    rw [List.toFinset_cons]
    change average (fixOn w (insert k ks.toFinset)
      (Function.update (chooseLayout score alphabet default ks (fixAt w k a)).1 k a)) f ≤ _
    rw [← fixOn_insert w hN']
    exact htail.trans (hb'.trans hb)

theorem chooseLayout_correct (score : Marginals P A → ℚ)
    (alphabet : List A) (default : A) (hall : ∀ a : A, a ∈ alphabet)
    (f : (P → A) → ℚ)
    (hscore : ∀ w : Marginals P A, (∀ i, ∑ a, w i a=1) → score w = average w f)
    (ks : List P) (hk : ks.Nodup) (cover : ∀ k : P, k ∈ ks) (w : Marginals P A)
    (h0 : ∀ i a, 0 ≤ w i a) (h1 : ∀ i, ∑ a, w i a=1) :
    f (chooseLayout score alphabet default ks w).1 ≤ average w f := by
  have h := chooseLayout_prefix score alphabet default hall f hscore ks hk w h0 h1
  have hfull : ks.toFinset = Finset.univ := by
    ext k
    suffices k ∈ ks by simpa
    exact cover k
  rwa [hfull, average_fixOn_univ] at h

end Driver

#print axioms better_le_left
#print axioms better_le_right
#print axioms choose_le_initial
#print axioms choose_le_candidate
#print axioms chooseLayout_calls
#print axioms chooseLayout_prefix
#print axioms chooseLayout_correct

end J1R43Literal