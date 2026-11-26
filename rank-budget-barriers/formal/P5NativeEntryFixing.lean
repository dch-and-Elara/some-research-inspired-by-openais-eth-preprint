import P5NativeEntryGreedy
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt

/-! Incidences and exact high-incidence threshold (source lines 3096–3145).
One neutral scope really contributes one incidence for each declared variable.
Rows are indexed by list position, even when they coincide. -/
namespace Paper5.NativeEntry
open scoped BigOperators

def degree {n : ℕ} (A : Rows n) (v : Fin n) : ℕ :=
  1+(Finset.univ.filter fun i : Fin A.length=>A.get i v≠0).card

def incidences {n : ℕ} (A : Rows n) : ℕ := ∑ v,degree A v

def ceilSqrt (m : ℕ) : ℕ :=
  if m.sqrt^2=m then m.sqrt else m.sqrt+1

theorem ceilSqrt_sq_ge (m : ℕ) : m≤(ceilSqrt m)^2 := by
  unfold ceilSqrt
  split_ifs with h
  · exact h.ge
  · exact (Nat.lt_succ_sqrt' m).le

def divUp (a n : ℕ) : ℕ := (a+n-1)/n

theorem le_mul_divUp (a n : ℕ) (hn : 0<n) : a≤n*divUp a n := by
  unfold divUp
  have hp := Nat.mod_add_div (a+n-1) n
  have hm := Nat.mod_lt (a+n-1) hn
  omega

def fixingThreshold {n : ℕ} (A : Rows n) : ℕ :=
  (divUp (incidences A) n)*ceilSqrt (Nat.clog 2 n)

def fixed {n : ℕ} (A : Rows n) : Finset (Fin n) :=
  Finset.univ.filter fun v => fixingThreshold A<degree A v

abbrev Free {n : ℕ} (A : Rows n) := ↥((fixed A)ᶜ)

def dim {n : ℕ} (A : Rows n) : ℕ := ((fixed A)ᶜ).card

@[simp] theorem free_card {n : ℕ} (A : Rows n) : Fintype.card (Free A)=dim A := by
  simp [dim]

theorem dim_add_fixed {n : ℕ} (A : Rows n) : dim A+(fixed A).card=n := by
  rw [dim,Finset.card_compl,Fintype.card_fin]
  exact Nat.sub_add_cancel (by simpa using Finset.card_le_univ (fixed A))

theorem count_incidence_neutral {n : ℕ} (A : Rows n) :
    n≤ incidences A := by
  change n≤∑ v : Fin n,(1+(Finset.univ.filter fun i : Fin A.length=>A.get i v≠0).card)
  simp [Finset.sum_add_distrib]

theorem incidences_by_row {n : ℕ} (A : Rows n) :
    incidences A=n+∑ i : Fin A.length,(support (A.get i)).card := by
  classical
  unfold incidences degree support
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,Nat.mul_one,Finset.card_filter]
  rw [Finset.sum_comm]

theorem fixed_scale {n : ℕ} (A : Rows n) (hn : 0<n) :
    (fixed A).card*ceilSqrt (Nat.clog 2 n)≤n := by
  let b := divUp (incidences A) n
  have hM : incidences A≤n*b := by simpa [b] using le_mul_divUp (incidences A) n hn
  have hb : 0<b := by
    by_contra! hh
    have hb0 : b=0 := by omega
    have hp := count_incidence_neutral A
    rw [hb0,Nat.mul_zero] at hM
    omega
  have hcard : (fixed A).card*fixingThreshold A≤ incidences A := by
    calc
      _ = ∑ _v ∈ fixed A, fixingThreshold A := by simp
      _ ≤ ∑ v ∈ fixed A,degree A v := by
        apply Finset.sum_le_sum
        intro v hv
        simpa only [fixed,Finset.mem_filter,true_and,Finset.mem_univ] using (Finset.mem_filter.mp hv).2.le
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.subset_univ _) 
  apply Nat.le_of_mul_le_mul_right _ hb
  calc
    _ = (fixed A).card*fixingThreshold A := by unfold fixingThreshold b; ring
    _ ≤ _ := hcard.trans hM

theorem dim_at_least_half {n : ℕ} (A : Rows n) (hn : 20≤n) : n≤2*dim A := by
  have h := fixed_scale A (by omega)
  have hLam : 4<Nat.clog 2 n := by
    apply (Nat.lt_clog_iff_pow_lt (by decide)).2
    omega
  have hb : 2≤ceilSqrt (Nat.clog 2 n) := by
    have hp := ceilSqrt_sq_ge (Nat.clog 2 n)
    by_contra! hh
    have hh' : (ceilSqrt (Nat.clog 2 n))^2≤1^2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have h' := (Nat.mul_le_mul_left (fixed A).card hb).trans h
  have he := dim_add_fixed A
  omega

theorem free_degree_cap {n : ℕ} (A : Rows n) (v : Free A) :
    degree A v≤fixingThreshold A := by
  have hv := v.property
  simpa [fixed,not_lt] using hv

def restrictedSupport {n : ℕ} (A : Rows n) (r : Word n) : Finset (Free A) :=
  Finset.univ.filter fun v=>r v≠0

@[simp] theorem mem_restricted_support {n : ℕ} (A : Rows n) (r : Word n) (v : Free A) :
    v∈restrictedSupport A r ↔ r v≠0 := by simp [restrictedSupport]

theorem width_after_fixing {n : ℕ} (A : Rows n) (r : Word n) :
    (restrictedSupport A r).card≤(support r).card := by
  apply Finset.card_le_card_of_injOn Subtype.val
  · intro v hv
    simpa using hv
  · exact Subtype.val_injective.injOn

def retained {n : ℕ} (A : Rows n) : Finset (Fin A.length) :=
  Finset.univ.filter fun i=> (restrictedSupport A (A.get i)).Nonempty

def branchIncidences {n : ℕ} (A : Rows n) : ℕ :=
  dim A+∑ i ∈ retained A,(restrictedSupport A (A.get i)).card

theorem branch_incidence_bounds {n W : ℕ} (A : Rows n) (hn : 20≤n)
    (hRows : A.length≤6*n) (hW : ∀ r∈A,(support r).card≤W) :
    dim A≤branchIncidences A ∧ branchIncidences A≤dim A*(1+12*W) := by
  refine ⟨Nat.le_add_right _ _,?_⟩
  have h1 : (retained A).card≤A.length := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (retained A))
  have h2 := dim_at_least_half A hn
  unfold branchIncidences
  calc
    _ ≤ dim A+∑ _i ∈ retained A,W := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro i _
      exact (width_after_fixing A _).trans (hW _ (List.get_mem _ _))
    _ = dim A+(retained A).card*W := by simp
    _ ≤ dim A+(6*(2*dim A))*W := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_right _ (h1.trans (hRows.trans (Nat.mul_le_mul_left _ h2)))) _
    _ = _ := by ring

theorem retained_bound {n : ℕ} (A : Rows n) :
    (retained A).card≤A.length := by
  simpa only [Finset.card_univ,Fintype.card_fin] using
    Finset.card_le_card (Finset.subset_univ (retained A))

theorem branch_scope_degree {n : ℕ} (A : Rows n) (v : Free A) :
    1+((retained A).filter fun i=>A.get i v≠0).card=degree A v := by
  unfold degree
  congr 1
  apply congrArg Finset.card
  ext i
  simp only [retained,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · exact And.right
  · intro hi
    exact ⟨⟨v,(mem_restricted_support _ _ _).mpr hi⟩,hi⟩

#print axioms ceilSqrt_sq_ge
#print axioms le_mul_divUp
#print axioms dim_add_fixed
#print axioms count_incidence_neutral
#print axioms incidences_by_row
#print axioms fixed_scale
#print axioms dim_at_least_half
#print axioms free_degree_cap
#print axioms width_after_fixing
#print axioms branch_incidence_bounds
#print axioms retained_bound
#print axioms branch_scope_degree
end Paper5.NativeEntry