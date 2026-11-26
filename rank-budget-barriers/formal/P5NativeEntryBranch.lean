import P5NativeEntryPolynomial

/-! The nonconstant correct branch reached from a full-column-rank
source query.  The restricted matrix is over its real free variables and
the retained original row indices, after the actual substitutions. -/
namespace Paper5.NativeEntry
open scoped BigOperators
open Module

abbrev Factors {n : ℕ} (A : Rows n) := Free A ⊕ ↥(retained A)
abbrev Ports {n : ℕ} (A : Rows n) :=
  Free A ⊕ (Σ i : ↥(retained A), ↥(restrictedSupport A (A.get i)))

def portOwner {n : ℕ} {A : Rows n} : Ports A → Free A
  | Sum.inl v => v
  | Sum.inr p => p.2

def portFactor {n : ℕ} {A : Rows n} : Ports A → Factors A
  | Sum.inl v => Sum.inl v
  | Sum.inr p => Sum.inr p.1

theorem ports_count {n : ℕ} (A : Rows n) : Fintype.card (Ports A)=branchIncidences A := by
  simp only [Ports,Fintype.card_sum,Fintype.card_sigma,Fintype.card_coe]
  rw [branchIncidences,dim]
  congr 1
  exact (Finset.sum_subtype (retained A) (fun _=>Iff.rfl)
    (fun i=>(restrictedSupport A (A.get i)).card)).symm

def zeroExtend {n : ℕ} (A : Rows n) (x : Free A → F₂) : Word n :=
  fun v=>if h : v∈(fixed A)ᶜ then x ⟨v,h⟩ else 0

theorem zero_extend_inj {n : ℕ} (A : Rows n) :
    Function.Injective (zeroExtend A) := by
  intro x y h
  funext v
  have hh := congrFun h v.val
  simpa only [zeroExtend,dif_pos v.property] using hh

theorem zero_extend_zero {n : ℕ} (A : Rows n) :
    zeroExtend A 0=0 := by
  funext v
  unfold zeroExtend
  split_ifs <;> rfl

theorem rowForm_extended {n : ℕ} (A : Rows n) (r : Word n) (x : Free A→F₂) :
    rowForm r (zeroExtend A x)=∑ v : Free A,r v*x v := by
  have hs := Finset.sum_attach_eq_sum_dite ((fixed A)ᶜ) (fun v : Free A=>r v*x v)
  rw [rowForm_apply,Finset.univ_eq_attach,hs]
  apply Finset.sum_congr rfl
  intro v _
  unfold zeroExtend
  split_ifs <;> simp

def branchMatrix {n : ℕ} (A : Rows n) : Matrix ↥(retained A) (Free A) F₂ :=
  fun i v=>A.get i v

theorem omitted_zero_coefficient {n : ℕ} (A : Rows n) (i : Fin A.length)
    (hi : i∉retained A) (v : Free A) : A.get i v=0 := by
  by_contra hh
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,⟨v,(mem_restricted_support _ _ _).mpr hh⟩⟩)

theorem branch_kernel_bottom {n : ℕ} (A : Rows n) (hA : (matrix A).rank=n) :
    LinearMap.ker (branchMatrix A).mulVecLin=⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  have hfull := (rank_eq_full_iff A).mp hA
  have hmem : zeroExtend A x∈kernel A := by
    apply (mem_kernel _ _).mpr
    intro r hr
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
    rw [rowForm_extended]
    by_cases hi : i∈retained A
    · have hh := congrFun ((LinearMap.mem_ker.mp hx) :
          (branchMatrix A).mulVecLin x=0) (⟨i,hi⟩ : ↥(retained A))
      exact hh
    · simp [omitted_zero_coefficient A i hi]
  have hzero : zeroExtend A x=0 := by simpa [hfull] using hmem
  apply zero_extend_inj A
  rw [zero_extend_zero,hzero]

theorem restricted_rank_exact {n : ℕ} (A : Rows n) (hA : (matrix A).rank=n) :
    (branchMatrix A).rank=dim A := by
  rw [Matrix.rank, LinearMap.finrank_range_of_inj
       (LinearMap.ker_eq_bot.mp (branch_kernel_bottom A hA)),finrank_pi,free_card]

theorem branch_has_equations {n : ℕ} (A : Rows n) (hn : 20≤n)
    (hA : (matrix A).rank=n) : 0<dim A ∧ dim A≤(retained A).card := by
  have h := dim_at_least_half A hn
  have hh := Matrix.rank_le_card_height (branchMatrix A)
  rw [restricted_rank_exact A hA,Fintype.card_coe] at hh
  exact ⟨by omega,hh⟩

def nominalPrecision (n : ℕ) : ℕ := n+1
def shapeDegree {n : ℕ} (k : ℕ) (A : Rows n) : ℕ :=
  k*((retained A).card+2*(nominalPrecision n-1))

theorem correct_branch_number_bounds {n k B : ℕ} (A : Rows n) (hn : 20≤n)
    (hA : (matrix A).rank=n) (hrows : A.length≤6*n)
    (hwidth : ∀ r∈A,(support r).card≤hashD₀ n B) :
    0<dim A ∧ n≤2*dim A ∧ dim A≤(retained A).card ∧
    dim A≤branchIncidences A ∧ branchIncidences A≤dim A*(1+12*hashD₀ n B) ∧
    dim A≤nominalPrecision n-1 ∧
    k*(dim A)≤shapeDegree k A ∧ shapeDegree k A≤16*k*(dim A) := by
  have ⟨hdim,htest⟩ := branch_has_equations A hn hA
  have hh := dim_at_least_half A hn
  have hg := dim_add_fixed A
  have hb := branch_incidence_bounds A hn hrows hwidth
  have htestU := (retained_bound A).trans hrows
  refine ⟨hdim,hh,htest,hb.1,hb.2,?_,?_,?_⟩
  · simp only [nominalPrecision,Nat.add_sub_cancel]
    omega
  · unfold shapeDegree
    exact Nat.mul_le_mul_left _ (htest.trans (Nat.le_add_right _ _))
  · unfold shapeDegree
    rw [show 16*k*dim A=k*(16*dim A) by ring]
    apply Nat.mul_le_mul_left
    simp only [nominalPrecision,Nat.add_sub_cancel]
    omega

theorem full_rank_source_query_branch {n B k : ℕ} {sgn : Fin n → Bool} {A₀ : Rows n}
    (run : @Greedy n (hashP n B) sgn A₀) (hn : 20≤n) (hB : 0<B)
    (hInit : A₀.length≤3*n) (hWidths : ∀ r∈A₀,(support r).card≤hashD₀ n B) :
    let A := run.rows (3*n)
    (matrix A).rank=n ∧ (branchMatrix A).rank=dim A ∧
    0<dim A ∧ n≤2*dim A ∧ dim A≤(retained A).card ∧
    dim A≤branchIncidences A ∧ branchIncidences A≤dim A*(1+12*hashD₀ n B) ∧
    dim A≤nominalPrecision n-1 ∧
    k*(dim A)≤shapeDegree k A ∧ shapeDegree k A≤16*k*(dim A) := by
  obtain ⟨hA,hrows,hW⟩ := final_source_rank_width run hB hInit hWidths
  exact ⟨hA,restricted_rank_exact _ hA,correct_branch_number_bounds _ hn hA hrows hW⟩

#print axioms ports_count
#print axioms zero_extend_inj
#print axioms rowForm_extended
#print axioms omitted_zero_coefficient
#print axioms branch_kernel_bottom
#print axioms restricted_rank_exact
#print axioms branch_has_equations
#print axioms correct_branch_number_bounds
#print axioms full_rank_source_query_branch
end Paper5.NativeEntry