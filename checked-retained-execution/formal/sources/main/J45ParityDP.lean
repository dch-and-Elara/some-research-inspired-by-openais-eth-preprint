import JointContraction
import J45CostLoops
import Mathlib.Data.Fintype.Powerset

/-! A finite, costed construction of the parity input table. It never takes
an oracle for whole completed products, equality classes, or moment values. -/
namespace J45Parity
open scoped BigOperators Classical
open JointContraction

section DenseGroup

variable {I R V : Type*} [AddCommGroup I] [Fintype I] [CommSemiring R]
  [DecidableEq V] {U : V → Type*} [∀ v,Fintype (U v)]

/-- One finite sweep, reading one old address per destination and local
assignment. At parity the subtraction is precisely XOR in each feature. -/
def groupStep (v : V) (w : ∀ v,U v→R) (inc : ∀ v,U v→I) (old : I→R) (j : I) : R :=
  ∑ z : U v, w v z*old (j-inc v z)

noncomputable def groupRun (w : ∀ v,U v→R) (inc : ∀ v,U v→I) : List V→I→R
  | [], j => if j=0 then 1 else 0
  | v::vs, j => groupStep v w inc (groupRun w inc vs) j

omit [Fintype I] in
theorem groupRun_exact (s : List V) (hs : s.Nodup) (w : ∀ v,U v→R)
    (inc : ∀ v,U v→I) (j : I) :
    groupRun w inc s j = distribution s.toFinset w inc j := by
  classical
  induction s generalizing j with
  | nil =>
    rw [groupRun,List.toFinset_nil,distribution_empty]
    by_cases hj : j=0 <;> simp [hj,AddMonoidAlgebra.one_def]
  | cons v vs ih =>
    rw [List.nodup_cons] at hs
    rw [groupRun,groupStep,List.toFinset_cons,
      distribution_insert_entry _ _ (by simpa using hs.1)]
    exact Finset.sum_congr rfl fun z _ => congrArg (w v z*·) (ih hs.2 _)

theorem group_readout_exact [Fintype V] (s : List V) (hs : s.Nodup)
    (full : s.toFinset=Finset.univ) (w : ∀ v,U v→R) (inc : ∀ v,U v→I) (m : I→R) :
    (∑ j, groupRun w inc s j*m j) = readout m (distribution Finset.univ w inc) := by
  classical
  simp_rw [groupRun_exact s hs,full,distribution_entry,Finset.sum_mul]
  rw [Finset.sum_comm,readout_distribution]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp

end DenseGroup

section Parity

variable {D : Type*} [Fintype D] [DecidableEq D]

abbrev Bits (D : Type*) := D→ZMod 2

def vector (s : Finset D) : Bits D := fun d => if d∈s then 1 else 0

def mask (x : Bits D) : Finset D := Finset.univ.filter fun d => x d = 1

def maskChart : Finset D ≃ Bits D where
  toFun := vector
  invFun := mask
  left_inv := by intro s; ext d; simp [mask,vector]
  right_inv := by
    intro x
    funext d
    change (if d∈mask x then (1:ZMod 2) else 0) = x d
    have he := (show d∈mask x ↔ x d=1 by simp [mask])
    by_cases hx : x d=1
    · rw [if_pos (he.mpr hx),hx]
    · rw [if_neg (fun h => hx (he.mp h))]
      generalize eq : x d = q at hx ⊢
      fin_cases q <;> simp_all

omit [Fintype D] in
theorem monomial_in_mask (S T : Finset D) :
    (∏ d∈S, vector T d) = if S⊆T then (1:ZMod 2) else 0 := by
  by_cases h : S⊆T
  · rw [if_pos h]
    exact Finset.prod_eq_one fun d hd => if_pos (h hd)
  · obtain ⟨d,hd,hno⟩ := Finset.not_subset.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero hd (if_neg hno)

/-- The weight-counting parity box has two states per actual feature. -/
theorem parity_visits {M V : Type*} [Fintype M] [Fintype V]
    (U : V→Type*) [∀ v,Fintype (U v)] :
    Fintype.card ((M→Bool) × (Bits D × (Σ v,U v))) =
      2^Fintype.card M * 2^Fintype.card D * ∑ v, Fintype.card (U v) := by
  classical
  simp [Bits,mul_assoc]

variable {A B M : Type*} [Fintype A] [Fintype B] [Fintype M]
    {P : A→Type*} {Q : B→Type*} [∀ a,Fintype (P a)] [∀ b,Fintype (Q b)]

/-- Construct the table from original local matrices, feature contributions,
and actual matched-bit addresses. The local parity stat is part of the
column payload; evaluating it is accounted for separately from coefficient
updates. -/
noncomputable def buildTable (s : List B) (ports : M→Sigma Q)
    (wire : ∀ a,P a→Option M) (unit : ZMod 2)
    (tabA : ∀ a,(P a→Bool)→ZMod 2) (tabB : ∀ b,(Q b→Bool)→ZMod 2)
    (inc : ∀ b,(Q b→Bool)→Bits D) (T : Finset D) : ZMod 2 :=
  ∑ w : M→Bool, rowValue wire unit tabA w *
    groupRun (fun b z => if agrees ports w b z then tabB b z else 0) inc s (vector T)

/-- Before any transform, the genuine finite parity table already answers
the native moment through its superset sum. -/
theorem buildTable_superset (s : List B) (hs : s.Nodup) (full : s.toFinset=Finset.univ)
    (ports : M→Sigma Q) (wire : ∀ a,P a→Option M) (unit : ZMod 2)
    (tabA : ∀ a,(P a→Bool)→ZMod 2) (tabB : ∀ b,(Q b→Bool)→ZMod 2)
    (inc : ∀ b,(Q b→Bool)→Bits D) (S : Finset D) :
    (∑ T : Finset D, if S⊆T then buildTable s ports wire unit tabA tabB inc T else 0) =
     ∑ x : (∀ b,Q b→Bool), ∑ y : (∀ a,P a→Bool),
      ((∏ a,tabA a (y a)) * ∏ a,∏ p,
        literal (y a p) (wiredInput unit (matchedBits ports x) (wire a p))) *
      ((∏ b,tabB b (x b)) * (∏ d∈S,(∑ b,inc b (x b)) d)) := by
  rw [joint_moment_contraction ports wire unit tabA tabB inc (fun x => ∏ d∈S,x d)]
  have hrep : ∀ T : Finset D,
      (if S⊆T then buildTable s ports wire unit tabA tabB inc T else 0) =
      buildTable s ports wire unit tabA tabB inc T * ∏ d∈S, vector T d := by
    intro T
    rw [monomial_in_mask]
    split_ifs <;> simp
  have hconvert : (∑ T : Finset D, if S⊆T then buildTable s ports wire unit tabA tabB inc T else 0) =
      ∑ T : Finset D, buildTable s ports wire unit tabA tabB inc T * ∏ d∈S,vector T d :=
    Finset.sum_congr rfl fun T _ => hrep T
  rw [hconvert]
  simp only [buildTable,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  have hsum : (∑ T : Finset D, groupRun (fun b z => if agrees ports w b z then tabB b z else 0)
      inc s (vector T) * (∏ d∈S,vector T d)) =
      ∑ x : Bits D, groupRun (fun b z => if agrees ports w b z then tabB b z else 0)
      inc s x * (∏ d∈S,x d) :=
    Fintype.sum_equiv maskChart _ _ (fun _ => rfl)
  rw [hsum,group_readout_exact s hs full]

end Parity

#print axioms groupRun_exact
#print axioms group_readout_exact
#print axioms maskChart
#print axioms monomial_in_mask
#print axioms parity_visits
#print axioms buildTable_superset

end J45Parity