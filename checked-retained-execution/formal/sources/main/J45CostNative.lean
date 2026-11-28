import J45CostDP
import J45CostLoops

/-! Composes the old literal matching-boundary semantics with the actual
finite arrays, retaining one across-pattern distribution for every query. -/
namespace J45Cost
open scoped BigOperators Classical
open JointContraction

section SourceRange

variable {B D : Type*} [Fintype B] {Q : B → Type*} [∀ b,Fintype (Q b)]

/-- The contribution of each original column vertex to each actual tile
mode. An absent bit contributes zero, a present bit its nonnegative weight. -/
def sourceIncrement (weight : ∀ b,Q b→D→ℕ) (b : B) (z : Q b→Bool) : D→ℕ :=
  fun d => ∑ q, if z q then weight b q d else 0

def sourceLimit (weight : ∀ b,Q b→D→ℕ) : D→ℕ :=
  fun d => ∑ b, ∑ q, weight b q d

theorem source_increment_bound (weight : ∀ b,Q b→D→ℕ) (a : ∀ b,Q b→Bool) (d : D) :
    (∑ b, sourceIncrement weight b (a b)) d ≤ sourceLimit weight d := by
  simp only [sourceLimit,Finset.sum_apply,sourceIncrement]
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro q _
  cases a b q <;> simp

/-- With the actual J5 power weights, the box is determined by the sum of
j^b over that tile (with 0^0=1), not by an arbitrary score bound. -/
def tileWeight {T : Type*} [DecidableEq T] (tile : ∀ b,Q b→T)
    (index : ∀ b,Q b→ℕ) (target : D→T) (power : D→ℕ) (b : B) (q : Q b) (d : D) : ℕ :=
  if tile b q=target d then (index b q)^power d else 0

theorem tile_limit_exact {T : Type*} [DecidableEq T] (tile : ∀ b,Q b→T)
    (index : ∀ b,Q b→ℕ) (target : D→T) (power : D→ℕ) (d : D) :
    sourceLimit (tileWeight tile index target power) d =
      ∑ v ∈ (Finset.univ : Finset (Σ b,Q b)).filter (fun v => tile v.1 v.2=target d),
        (index v.1 v.2)^power d := by
  classical
  rw [Finset.sum_filter,Fintype.sum_sigma]
  rfl

end SourceRange

section Execution

variable {A B M D R : Type*} [Fintype A] [Fintype B] [Fintype M] [Fintype D]
    [CommRing R]
    {P : A → Type*} {Q : B → Type*} [∀ a,Fintype (P a)] [∀ b,Fintype (Q b)]

/-- A single across-boundary result array, obtained by adding the current
child's column DP, scaled by the actual row contraction. -/
noncomputable def combinedTable (H : D→ℕ) (s : List B) (ports : M→Sigma Q)
    (wire : ∀ a,P a→Option M) (unit : R) (tabA : ∀ a,(P a→Bool)→R)
    (tabB : ∀ b,(Q b→Bool)→R) (inc : ∀ b,(Q b→Bool)→D→ℕ) : Box H→R :=
  fun x => ∑ w : M→Bool, rowValue wire unit tabA w *
    dpRun H (fun b z => if agrees ports w b z then tabB b z else 0) inc s x

/-- Each result from the shared table equals the immutable source sum
with that exact moment. Neither signs nor repeated moments are restricted. -/
theorem combinedTable_exact (H : D→ℕ) (s : List B) (nh : s.Nodup) (sh : s.toFinset = Finset.univ)
    (ports : M→Sigma Q) (wire : ∀ a,P a→Option M) (unit : R) (tabA : ∀ a,(P a→Bool)→R)
    (tabB : ∀ b,(Q b→Bool)→R) (inc : ∀ b,(Q b→Bool)→D→ℕ) (moment : (D→ℤ)→R)
    (bound : ∀ a : (∀ b,Q b→Bool), ∀ d, (∑ b, inc b (a b)) d ≤ H d) :
    (∑ x : Box H, combinedTable H s ports wire unit tabA tabB inc x * moment (intIndex H x)) =
     ∑ x : (∀ b,Q b→Bool), ∑ y : (∀ a,P a→Bool),
      ((∏ a,tabA a (y a)) * ∏ a,∏ p,
        literal (y a p) (wiredInput unit (matchedBits ports x) (wire a p))) *
      ((∏ b,tabB b (x b)) * moment (∑ b,intInc inc b (x b))) := by
  rw [joint_moment_contraction ports wire unit tabA tabB (intInc inc) moment]
  unfold combinedTable
  simp only [Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.mul_sum,finite_readout_exact H s nh sh _ inc moment bound]

/-- Stage table computation and subsequent repeated queries reuse the exact
same bound H_d from the sum of the physical tile weights. -/
theorem native_source_table_exact (s : List B) (nh : s.Nodup) (sh : s.toFinset=Finset.univ)
    (ports : M→Sigma Q) (wire : ∀ a,P a→Option M) (unit : R)
    (tabA : ∀ a,(P a→Bool)→R) (tabB : ∀ b,(Q b→Bool)→R) (weight : ∀ b,Q b→D→ℕ)
    (moment : (D→ℤ) → R) :
    let H := sourceLimit weight
    (∑ z : Box H, combinedTable H s ports wire unit tabA tabB (sourceIncrement weight) z *
        moment (intIndex H z)) =
     ∑ x : (∀ b,Q b→Bool), ∑ y : (∀ a,P a→Bool),
      ((∏ a,tabA a (y a)) * ∏ a,∏ p,
        literal (y a p) (wiredInput unit (matchedBits ports x) (wire a p))) *
      ((∏ b,tabB b (x b)) * moment (∑ b,intInc (sourceIncrement weight) b (x b))) :=
  combinedTable_exact _ s nh sh ports wire unit tabA tabB (sourceIncrement weight) moment
    (source_increment_bound weight)

end Execution

#print axioms source_increment_bound
#print axioms tile_limit_exact
#print axioms combinedTable_exact
#print axioms native_source_table_exact

end J45Cost