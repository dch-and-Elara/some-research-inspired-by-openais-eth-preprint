import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace P6Joint
open scoped BigOperators

section AdjacentCuts
variable {K X A B : Type*} [CommSemiring K] [Fintype X] [Fintype A] [Fintype B]
open Classical

def cutContraction (left : X → A → K) (right : X → B → K) : K :=
  ∑ x, ∑ a, ∑ b, left x a * right x b

theorem cutContraction_eq (left : X → A → K) (right : X → B → K) :
    cutContraction left right = ∑ x, (∑ a, left x a) * (∑ b, right x b) := by
  simp only [cutContraction, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

/-- The very same two messages can be reused for different middle factors;
no inverse of a message is required. -/
theorem substitute_at_cut (left : X → A → K) (right : X → B → K)
    (middle : X → K) :
    (∑ x, ∑ a, ∑ b, left x a * middle x * right x b) =
    ∑ x, (∑ a, left x a) * middle x * (∑ b, right x b) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

end AdjacentCuts

/-- Each constructor is one legal table contraction operation. Its index is
the maximum number of active boundary variables at this node, with domain D.
Restriction and input factor evaluations live in table reads
and are not counted as arithmetic gates by this module. -/
inductive BoundaryPlan (D K : Type*) : ℕ → Type _
  | leaf {k} (read : (Fin k → D) → K) : BoundaryPlan D K k
  | join {k} (left right : BoundaryPlan D K k) : BoundaryPlan D K k
  | introduce {k} (child : BoundaryPlan D K k) : BoundaryPlan D K (k+1)
  | relabel {k} (perm : Fin k ≃ Fin k) (child : BoundaryPlan D K k) : BoundaryPlan D K k
  | forget {k} (child : BoundaryPlan D K (k+1)) : BoundaryPlan D K k

namespace BoundaryPlan

universe u v
variable {D : Type u} {K : Type v} [Fintype D] [CommSemiring K]

def denotation : {k : ℕ} → BoundaryPlan D K k → (Fin k → D) → K
  | _, .leaf read, x => read x
  | _, .join l r, x => denotation l x * denotation r x
  | _, .introduce p, x => denotation p (fun i => x i.succ)
  | _, .relabel perm p, x => denotation p (x ∘ perm)
  | _, .forget p, x => ∑ a : D, denotation p (Fin.cons a x)

def nodes : {k : ℕ} → BoundaryPlan D K k → ℕ
  | _, .leaf _ => 1
  | _, .join l r => nodes l + nodes r + 1
  | _, .introduce p => nodes p + 1
  | _, .relabel _ p => nodes p + 1
  | _, .forget p => nodes p + 1

def arity {k : ℕ} (_ : BoundaryPlan D K k) : ℕ := k

def width : {k : ℕ} → BoundaryPlan D K k → ℕ
  | k, .leaf _ => k
  | _, .join l r => max (width l) (width r)
  | _, .introduce p => max (arity p + 1) (width p)
  | _, .relabel _ p => width p
  | _, .forget p => width p

/-- Charged arithmetic of a full table at each node, one operation per
join entry or per input to the forget sum (zero-starting convention).
Includes no per-table input generation or indexing costs. -/
def tableOps : {k : ℕ} → BoundaryPlan D K k → ℕ
  | _, .leaf _ => 0
  | k, .join l r => tableOps l + tableOps r + Fintype.card D ^ k
  | _, .introduce p => tableOps p
  | _, .relabel _ p => tableOps p
  | k, .forget p => tableOps p + Fintype.card D ^ (k+1)

omit [Fintype D] [CommSemiring K] in theorem index_le_width {k : ℕ} (p : BoundaryPlan D K k) : k ≤ width p := by
  induction p with
  | leaf => simp [width]
  | join l r ihl ihr =>
    simp only [width]
    exact ihl.trans (le_max_left _ _)
  | introduce p ih =>
    simp only [width, arity]
    exact le_max_left _ _
  | relabel _ p ih => exact ih
  | forget p ih => exact (Nat.le_succ _).trans ih

omit [CommSemiring K] in theorem tableOps_le {k w : ℕ} (p : BoundaryPlan D K k) (hw : width p ≤ w)
    (hD : 0 < Fintype.card D) :
    tableOps p ≤ nodes p * Fintype.card D ^ w := by
  induction p with
  | leaf => simp [tableOps]
  | @join k l r ihl ihr =>
    simp only [width] at hw
    have hl := ihl ((le_max_left _ _).trans hw)
    have hr := ihr ((le_max_right _ _).trans hw)
    have hk := Nat.pow_le_pow_right hD ((index_le_width (.join l r)).trans hw)
    simp only [tableOps, nodes, Nat.add_mul, Nat.one_mul]
    omega
  | @introduce k p ih =>
    simp only [width] at hw
    have hp := ih ((le_max_right _ _).trans hw)
    simp only [tableOps, nodes, Nat.add_mul, Nat.one_mul]
    omega
  | relabel _ p ih =>
    have hp := ih hw
    simp only [tableOps, nodes, Nat.add_mul, Nat.one_mul]
    omega
  | @forget k p ih =>
    have hp := ih hw
    have hk := Nat.pow_le_pow_right hD ((index_le_width p).trans hw)
    simp only [tableOps, nodes, Nat.add_mul, Nat.one_mul]
    omega

/-- Explicit factor product over the independent assignments introduced
by each forget operation. Join pairs config variables, while boundary
variables are identically glued by the shared boundary argument. -/
def Config : {k : ℕ} → BoundaryPlan D K k → Type u
  | _, .leaf _ => PUnit
  | _, .join l r => Config l × Config r
  | _, .introduce p => Config p
  | _, .relabel _ p => Config p
  | _, .forget p => D × Config p

noncomputable def configFintype : {k : ℕ} → (p : BoundaryPlan D K k) → Fintype (Config p)
  | _, .leaf _ => inferInstanceAs (Fintype PUnit)
  | _, .join l r =>
    letI := configFintype l
    letI := configFintype r
    inferInstanceAs (Fintype (Config l × Config r))
  | _, .introduce p => configFintype p
  | _, .relabel _ p => configFintype p
  | _, .forget p =>
    letI := configFintype p
    inferInstanceAs (Fintype (D × Config p))

noncomputable instance instConfigFintype {k : ℕ} (p : BoundaryPlan D K k) :
    Fintype (Config p) := configFintype p

def raw : {k : ℕ} → (p : BoundaryPlan D K k) → (Fin k → D) → Config p → K
  | _, .leaf read, x, _ => read x
  | _, .join l r, x, c => raw l x c.1 * raw r x c.2
  | _, .introduce p, x, c => raw p (fun i => x i.succ) c
  | _, .relabel perm p, x, c => raw p (x ∘ perm) c
  | _, .forget p, x, c => raw p (Fin.cons c.1 x) c.2

theorem denotation_eq_raw {k : ℕ} (p : BoundaryPlan D K k) (x : Fin k → D) :
    denotation p x = ∑ c : Config p, raw p x c := by
  classical
  induction p with
  | leaf read =>
    simp [denotation, raw, Config, instConfigFintype, configFintype]
  | join l r ihl ihr =>
    change denotation l x * denotation r x =
      @Finset.sum (Config l × Config r) K _ Finset.univ
        (fun c => raw l x c.1 * raw r x c.2)
    rw [ihl, ihr]
    rw [Fintype.sum_prod_type] 
    simp only [Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_comm
  | introduce p ih => exact ih _
  | relabel _ p ih => exact ih _
  | forget p ih =>
    change (∑ a : D, denotation p (Fin.cons a x)) =
      @Finset.sum (D × Config p) K _ Finset.univ
        (fun c => raw p (Fin.cons c.1 x) c.2)
    simp [ih, Fintype.sum_prod_type]

/-- A supplied decomposition can be checked with its assignment equivalence
and its pointwise factor product, not by assuming partition-sum equality. -/
theorem denotation_eq_partition_of_witness {k : ℕ} {Ω : Type*} [Fintype Ω]
    (p : BoundaryPlan D K k) (x : Fin k → D) (a : Ω ≃ Config p) (factorProduct : Ω → K)
    (h : ∀ c, raw p x (a c) = factorProduct c) :
    denotation p x = ∑ c, factorProduct c := by
  rw [denotation_eq_raw]
  exact (Fintype.sum_equiv a _ _ (fun x => (h x).symm)).symm

 
omit [CommSemiring K] in
/-- Per-probe pool: one plan for each distinct local partition or marked
marginal. Reuse across output modes is by indexing this pool. Here the
tariff is an upper bound per ring arithmetic operation, not a proof of
a bit implementation of ring reads or an indexer. -/
theorem pooled_table_arithmetic_cost
    {I : Type*} [Fintype I] (ar : I → ℕ)
    (p : ∀ i, BoundaryPlan D K (ar i)) (w tariff : ℕ)
    (hw : ∀ i, width (p i) ≤ w) (hD : 0 < Fintype.card D) :
    (∑ i, tableOps (p i) * tariff) ≤
      (∑ i, nodes (p i)) * Fintype.card D ^ w * tariff := by
  classical
  simp only [← Finset.sum_mul]
  apply Nat.mul_le_mul_right
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => tableOps_le (p i) (hw i) hD

 
/-- Padding a variable's alphabet with forbidden states is also allowed:
the additional configurations must carry zero weight pointwise. -/
theorem from_padded_assignment {k : ℕ} {Ω : Type*} [Fintype Ω]
    (p : BoundaryPlan D K k) (x : Fin k → D) (a : Ω ↪ Config p)
    (factorProduct : Ω → K)
    (h : ∀ c, raw p x (a c) = factorProduct c)
    (zeroOutside : ∀ c, c ∉ Set.range a → raw p x c = 0) :
    denotation p x = ∑ c, factorProduct c := by
  classical
  rw [denotation_eq_raw]
  let rs := (Finset.univ : Finset Ω).map a
  have hh : (∑ c ∈ rs, raw p x c) = ∑ c, factorProduct c := by
    unfold rs
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun c _ => h c
  rw [← hh]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro c _ hc
  apply zeroOutside c
  rintro ⟨b, rfl⟩
  apply hc
  exact Finset.mem_map.mpr ⟨b, Finset.mem_univ _, rfl⟩

end BoundaryPlan

#print axioms cutContraction_eq
#print axioms substitute_at_cut
#print axioms BoundaryPlan.tableOps_le
#print axioms BoundaryPlan.from_padded_assignment
#print axioms BoundaryPlan.pooled_table_arithmetic_cost
#print axioms BoundaryPlan.denotation_eq_partition_of_witness
end P6Joint
