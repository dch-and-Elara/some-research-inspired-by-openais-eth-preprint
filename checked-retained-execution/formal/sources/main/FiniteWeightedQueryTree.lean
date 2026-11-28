import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
An adaptive decoder chooses its next address as a function of its previous
reply. Two inputs per pattern have opposite required outputs. Away from a
query's support cylinder both inputs return the same public zero value.
The bound below concerns the cost of a run on an actual input.
-/

namespace FiniteWeightedQueryTree

universe u v w

inductive DecisionTree (Q : Type u) (R : Type v) : Type (max u v) where
  | leaf (output : Bool)
  | ask (query : Q) (next : R → DecisionTree Q R)

variable {Q : Type u} {R : Type v} {W : Type w}

def evaluate (oracle : Q → R) : DecisionTree Q R → Bool
  | .leaf output => output
  | .ask query next => evaluate oracle (next (oracle query))

def paid (cost : Q → ℕ) (oracle : Q → R) : DecisionTree Q R → ℕ
  | .leaf _ => 0
  | .ask query next => cost query + paid cost oracle (next (oracle query))

/-- Cardinality covered by one paid path, with an actual witness. -/
theorem actual_path_capacity [DecidableEq W] (zero : R)
    (oracle : W → Bool → Q → R) (support : Q → Finset W) (cost : Q → ℕ)
    (off : ∀ w b q, w ∉ support q → oracle w b q = zero)
    (cap : ∀ q, (support q).card ≤ cost q) (tree : DecisionTree Q R) :
    ∀ (pool : Finset W), pool.Nonempty →
      (∀ w ∈ pool, ∀ b, evaluate (oracle w b) tree = b) →
      ∃ w ∈ pool, ∃ b, pool.card ≤ paid cost (oracle w b) tree := by
  classical
  induction tree with
  | leaf value =>
    intro pool hn correct
    obtain ⟨w, hw⟩ := hn
    have h0 : value = false := correct w hw false
    have h1 : value = true := correct w hw true
    cases h0.symm.trans h1
  | ask q next ih =>
    intro pool hn correct
    let remaining := pool \ support q
    have subset : pool ⊆ remaining ∪ support q := by
      intro w hw
      by_cases hs : w ∈ support q
      · exact Finset.mem_union_right _ hs
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hw, hs⟩)
    have split : pool.card ≤ remaining.card + (support q).card :=
      (Finset.card_le_card subset).trans (Finset.card_union_le _ _)
    by_cases hr : remaining.Nonempty
    · have correct' : ∀ w ∈ remaining, ∀ b, evaluate (oracle w b) (next zero) = b := by
        intro w hw b
        have hw' := Finset.mem_sdiff.mp hw
        simpa only [evaluate, off w b q hw'.2] using correct w hw'.1 b
      obtain ⟨w, hw, b, htail⟩ := ih zero remaining hr correct'
      have hw' := Finset.mem_sdiff.mp hw
      refine ⟨w, hw'.1, b, ?_⟩
      simp only [paid, off w b q hw'.2]
      have hc := cap q
      omega
    · have hempty : remaining = ∅ := Finset.not_nonempty_iff_eq_empty.mp hr
      have hc : pool.card ≤ cost q := by
        simpa [hempty] using split.trans (Nat.add_le_add_left (cap q) remaining.card)
      obtain ⟨w, hw⟩ := hn
      exact ⟨w, hw, false, hc.trans (Nat.le_add_right _ _)⟩

theorem paid_constant (c : ℕ) (oracle : Q → R) (tree : DecisionTree Q R) :
    paid (fun _ => c) oracle tree = c * paid (fun _ => 1) oracle tree := by
  induction tree with
  | leaf value => simp [paid]
  | ask q next ih => simp [paid, ih, Nat.mul_add]

theorem actual_query_count [DecidableEq W] (zero : R)
    (oracle : W → Bool → Q → R) (support : Q → Finset W) (capacity : ℕ)
    (off : ∀ w b q, w ∉ support q → oracle w b q = zero)
    (cap : ∀ q, (support q).card ≤ capacity) (tree : DecisionTree Q R)
    (pool : Finset W) (hn : pool.Nonempty)
    (correct : ∀ w ∈ pool, ∀ b, evaluate (oracle w b) tree = b) :
    ∃ w ∈ pool, ∃ b, pool.card ≤ capacity * paid (fun _ => 1) (oracle w b) tree := by
  obtain ⟨w, hw, b, h⟩ :=
    actual_path_capacity zero oracle support (fun _ => capacity) off cap tree pool hn correct
  exact ⟨w, hw, b, (paid_constant capacity (oracle w b) tree) ▸ h⟩

/-- The embedding parameterizes a cylinder by its unqueried coordinates. -/
def freeCoordinates {S T : Type*} (e : W ≃ S × T) (s : S) : T ↪ W where
  toFun t := e.symm (s,t)
  inj' _ _ h := congrArg Prod.snd (e.symm.injective h)

def cylinder {S T : Type*} [Fintype T] (e : W ≃ S × T) (s : S) : Finset W :=
  Finset.univ.map (freeCoordinates e s)

theorem cylinder_card {S T : Type*} [Fintype T] (e : W ≃ S × T) (s : S) :
    (cylinder e s).card = Fintype.card T := by
  simp [cylinder]

theorem binary_cylinder_card {S : Type*} {free : ℕ}
    (e : W ≃ S × (Fin free → Bool)) (s : S) :
    (cylinder e s).card = 2 ^ free := by
  simp [cylinder_card]

theorem bit_pattern_capacity {k : ℕ} (zero : R)
    (oracle : (Fin k → Bool) → Bool → Q → R)
    (support : Q → Finset (Fin k → Bool)) (cost : Q → ℕ)
    (off : ∀ w b q, w ∉ support q → oracle w b q = zero)
    (cap : ∀ q, (support q).card ≤ cost q) (tree : DecisionTree Q R)
    (correct : ∀ w b, evaluate (oracle w b) tree = b) :
    ∃ w b, 2 ^ k ≤ paid cost (oracle w b) tree := by
  classical
  obtain ⟨w, _, b, h⟩ :=
    actual_path_capacity zero oracle support cost off cap tree Finset.univ
      Finset.univ_nonempty (fun w _ b => correct w b)
  exact ⟨w, b, by simpa using h⟩

#print axioms actual_path_capacity
#print axioms actual_query_count
#print axioms binary_cylinder_card
#print axioms bit_pattern_capacity

end FiniteWeightedQueryTree


