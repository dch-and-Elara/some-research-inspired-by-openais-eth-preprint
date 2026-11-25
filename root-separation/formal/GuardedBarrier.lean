import OverlappingRank

/-!
# Guard-aware transcript bounds

Branch outcomes may depend on the input. For each term, its two declared
views contain the arguments to their own transcript guard functions.
-/

namespace GuardedBarrier

open scoped BigOperators
open SeparatedRank OverlappingRank

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- A leaf's transcript predicates can be grouped into a guard for each
declared view. The augmented views include every argument to these guards. -/
structure GuardedTerm (ι K : Type*) extends ViewTerm ι K where
  firstGuard : (firstRows → Bool) → (firstCols → Bool) → Bool
  secondGuard : (secondRows → Bool) → (secondCols → Bool) → Bool

namespace GuardedTerm

def passes (t : GuardedTerm ι K) (x y : ι → Bool) : Bool :=
  t.firstGuard (CutTerm.restrict t.firstRows x) (CutTerm.restrict t.firstCols y) &&
    t.secondGuard (CutTerm.restrict t.secondRows x) (CutTerm.restrict t.secondCols y)

/-- Multiplying the local guards into their own factors preserves their
declared input scopes. -/
def masked (t : GuardedTerm ι K) : ViewTerm ι K :=
  { t.toViewTerm with
    first := fun x y => if t.firstGuard x y then t.first x y else 0
    second := fun x y => if t.secondGuard x y then t.second x y else 0 }

omit [Fintype ι] [DecidableEq ι] in
theorem masked_apply (t : GuardedTerm ι K) (x y : ι → Bool) :
    t.masked.matrix x y = if t.passes x y then t.toViewTerm.matrix x y else 0 := by
  cases h₁ : t.firstGuard (CutTerm.restrict t.firstRows x) (CutTerm.restrict t.firstCols y) <;>
    cases h₂ : t.secondGuard (CutTerm.restrict t.secondRows x) (CutTerm.restrict t.secondCols y) <;>
    simp [masked, ViewTerm.matrix, passes, h₁, h₂]

end GuardedTerm

omit [Fintype ι] [DecidableEq ι] in
/-- Sum all guarded leaf terms. On each assignment, exactly the actual
transcript contributes, while each leaf can have a different number of terms. -/
theorem guarded_matrix_sum {L : Type*} [Fintype L] {T : L → Type*} [∀ leaf, Fintype (T leaf)]
    (terms : (leaf : L) → T leaf → GuardedTerm ι K) (route : (ι → Bool) → (ι → Bool) → L)
    (hguard : ∀ leaf j x y, (terms leaf j).passes x y = true ↔ route x y = leaf)
    (M : Matrix (ι → Bool) (ι → Bool) K)
    (hvalue : ∀ x y, M x y = ∑ j, (terms (route x y) j).toViewTerm.matrix x y) :
    M = ∑ p : Σ leaf, T leaf, (terms p.1 p.2).masked.matrix := by
  classical
  ext x y
  rw [hvalue, Matrix.sum_apply, Fintype.sum_sigma]
  symm
  rw [Finset.sum_eq_single (route x y)]
  · apply Finset.sum_congr rfl
    intro j _
    rw [GuardedTerm.masked_apply, if_pos ((hguard _ j x y).2 rfl)]
  · intro leaf _ hne
    apply Finset.sum_eq_zero
    intro j _
    rw [GuardedTerm.masked_apply, if_neg (fun h => hne ((hguard leaf j x y).1 h).symm)]
  · simp

/-- At most `2^b` transcript labels, each with its own guarded terms and
cut choices, give the multiplicative form of equation (H). -/
theorem adaptive_barrier (b h d l : ℕ) {L : Type*} [Fintype L] {T : L → Type*}
    [∀ leaf, Fintype (T leaf)] (terms : (leaf : L) → T leaf → GuardedTerm ι K)
    (route : (ι → Bool) → (ι → Bool) → L) (hlabels : Fintype.card L ≤ 2 ^ b)
    (hguard : ∀ leaf j x y, (terms leaf j).passes x y = true ↔ route x y = leaf)
    (M : Matrix (ι → Bool) (ι → Bool) K)
    (hvalue : ∀ x y, M x y = ∑ j, (terms (route x y) j).toViewTerm.matrix x y)
    (hfull : M.rank = 2 ^ Fintype.card ι) (quota : ∀ leaf, Fintype.card (T leaf) ≤ h)
    (rows cols : (Σ leaf, T leaf) → Finset ι)
    (hexcess : ∀ p, d ≤ (rows p).card - (cols p).card)
    (hleak : ∀ p, (terms p.1 p.2).toViewTerm.leakage (rows p) (cols p) ≤ l) :
    2 ^ d ≤ 2 ^ (b + l) * h := by
  have hports := overlap_barrier (fun p : Σ leaf, T leaf => (terms p.1 p.2).masked)
    rows cols M hfull (guarded_matrix_sum terms route hguard M hvalue) d l hexcess hleak
  have hcount : Fintype.card (Σ leaf, T leaf) ≤ 2 ^ b * h := by
    rw [Fintype.card_sigma]
    calc
      _ ≤ ∑ _leaf : L, h := Finset.sum_le_sum fun leaf _ => quota leaf
      _ = Fintype.card L * h := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hlabels
  calc
    2 ^ d ≤ 2 ^ ((d - l) + l) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 2 ^ (d - l) * 2 ^ l := pow_add _ _ _
    _ ≤ (2 ^ b * h) * 2 ^ l := Nat.mul_le_mul_right _ (hports.trans hcount)
    _ = 2 ^ (b + l) * h := by rw [pow_add]; ac_rfl

/-- A finite binary decision tree with an arbitrary test at each branch. -/
inductive QueryTree (X : Type*) where
  | stop
  | query (test : X → Bool) (no yes : QueryTree X)

namespace QueryTree

variable {X : Type*}

def Leaf : QueryTree X → Type
  | .stop => Unit
  | .query _ no yes => no.Leaf ⊕ yes.Leaf

private def fintypeLeaf : (tree : QueryTree X) → Fintype tree.Leaf
  | .stop => inferInstanceAs (Fintype Unit)
  | .query _ no yes =>
    letI := fintypeLeaf no
    letI := fintypeLeaf yes
    inferInstanceAs (Fintype (no.Leaf ⊕ yes.Leaf))

instance (tree : QueryTree X) : Fintype tree.Leaf := fintypeLeaf tree

def depth : QueryTree X → ℕ
  | .stop => 0
  | .query _ no yes => max no.depth yes.depth + 1

def run : (tree : QueryTree X) → X → tree.Leaf
  | .stop, _ => ()
  | .query test no yes, x => if test x then .inr (yes.run x) else .inl (no.run x)

/-- The signed tests on a path include the negation of each false branch. -/
def path : (tree : QueryTree X) → tree.Leaf → List (X → Bool)
  | .stop, _ => []
  | .query test no _, .inl leaf => (fun x => !(test x)) :: no.path leaf
  | .query test _ yes, .inr leaf => test :: yes.path leaf

/-- The complete transcript predicate characterizes exactly the reached leaf. -/
theorem path_all_iff (tree : QueryTree X) (leaf : tree.Leaf) (x : X) :
    (tree.path leaf).all (fun p => p x) = true ↔ tree.run x = leaf := by
  induction tree with
  | stop => cases leaf; simp [path, run]
  | query test no yes hn hy =>
    cases leaf with
    | inl leaf =>
      cases hx : test x <;> simp [path, run, hx, hn]
      exact ⟨congrArg Sum.inl, Sum.inl.inj⟩
    | inr leaf =>
      cases hx : test x <;> simp [path, run, hx, hy]
      exact ⟨congrArg Sum.inr, Sum.inr.inj⟩

/-- The number of leaves follows from the actual tree depth. -/
theorem card_leaf_le (tree : QueryTree X) : Fintype.card tree.Leaf ≤ 2 ^ tree.depth := by
  induction tree with
  | stop => change Fintype.card Unit ≤ 2 ^ 0; simp
  | query test no yes hn hy =>
    change Fintype.card (no.Leaf ⊕ yes.Leaf) ≤ 2 ^ (max no.depth yes.depth + 1)
    rw [Fintype.card_sum, pow_succ, Nat.mul_two]
    exact Nat.add_le_add
      (hn.trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _)))
      (hy.trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _)))

end QueryTree

/-- A branch test, including the required outcome, on one declared view of a term. -/
inductive LocalTest (t : ViewTerm ι K) where
  | first (guard : (t.firstRows → Bool) → (t.firstCols → Bool) → Bool)
  | second (guard : (t.secondRows → Bool) → (t.secondCols → Bool) → Bool)

namespace LocalTest

variable {t : ViewTerm ι K}

def firstCheck : LocalTest t → (t.firstRows → Bool) → (t.firstCols → Bool) → Bool
  | .first guard, x, y => guard x y
  | .second _, _, _ => true

def secondCheck : LocalTest t → (t.secondRows → Bool) → (t.secondCols → Bool) → Bool
  | .first _, _, _ => true
  | .second guard, x, y => guard x y

def eval (g : LocalTest t) (xy : (ι → Bool) × (ι → Bool)) : Bool :=
  g.firstCheck (CutTerm.restrict t.firstRows xy.1) (CutTerm.restrict t.firstCols xy.2) &&
    g.secondCheck (CutTerm.restrict t.secondRows xy.1) (CutTerm.restrict t.secondCols xy.2)

/-- Group all the first-view tests together and all the second-view tests
together. Each group reads only its declared view. -/
def attach (t : ViewTerm ι K) (tests : List (LocalTest t)) : GuardedTerm ι K :=
  { toViewTerm := t
    firstGuard := fun x y => tests.all fun g => g.firstCheck x y
    secondGuard := fun x y => tests.all fun g => g.secondCheck x y }

omit [Fintype ι] [DecidableEq ι] [Field K] in
theorem attach_passes (tests : List (LocalTest t)) (x y : ι → Bool) :
    (attach t tests).passes x y = tests.all (fun g => g.eval (x, y)) := by
  induction tests with
  | nil => simp [GuardedTerm.passes, attach]
  | cons g rest ih =>
    simp only [GuardedTerm.passes, attach, List.all_cons, eval] at *
    rw [← ih]
    ac_rfl

end LocalTest

/-- The adaptive bound for an actual binary query tree. Each signed path test
is supplied as a predicate on one of the term's two views. Its equality to the
tree's path predicate is required pointwise as an equality of functions. -/
theorem tree_barrier (b h d l : ℕ) (tree : QueryTree ((ι → Bool) × (ι → Bool)))
    (hdepth : tree.depth ≤ b) {T : tree.Leaf → Type*} [∀ leaf, Fintype (T leaf)]
    (terms : (leaf : tree.Leaf) → T leaf → ViewTerm ι K)
    (guards : ∀ leaf j, List (LocalTest (terms leaf j)))
    (hpath : ∀ leaf j, (guards leaf j).map LocalTest.eval = tree.path leaf)
    (M : Matrix (ι → Bool) (ι → Bool) K)
    (hvalue : ∀ x y, M x y = ∑ j, (terms (tree.run (x, y)) j).matrix x y)
    (hfull : M.rank = 2 ^ Fintype.card ι) (quota : ∀ leaf, Fintype.card (T leaf) ≤ h)
    (rows cols : (Σ leaf, T leaf) → Finset ι)
    (hexcess : ∀ p, d ≤ (rows p).card - (cols p).card)
    (hleak : ∀ p, (terms p.1 p.2).leakage (rows p) (cols p) ≤ l) :
    2 ^ d ≤ 2 ^ (b + l) * h := by
  apply adaptive_barrier b h d l (fun leaf j => LocalTest.attach _ (guards leaf j))
    (fun x y => tree.run (x, y))
    (tree.card_leaf_le.trans (Nat.pow_le_pow_right (by decide) hdepth)) _ M hvalue
    hfull quota rows cols hexcess hleak
  intro leaf j x y
  rw [LocalTest.attach_passes]
  have h := tree.path_all_iff leaf (x, y)
  rw [← hpath leaf j] at h
  simpa only [List.all_map, Function.comp_apply] using h

#print axioms GuardedTerm.masked_apply
#print axioms guarded_matrix_sum
#print axioms adaptive_barrier
#print axioms QueryTree.path_all_iff
#print axioms QueryTree.card_leaf_le
#print axioms LocalTest.attach_passes
#print axioms tree_barrier

end GuardedBarrier
