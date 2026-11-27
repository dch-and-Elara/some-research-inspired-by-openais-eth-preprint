import P2PublishedFiltrationBasis

/-! The literal degree/divisibility filtration of Paper 2, not the
packed coefficient subset used by the existing mismatch theorem. A
bound n means degree < n, so n=0 encodes the paper's H_{−1}. -/
namespace Reconstruction.LayoutMismatch.PublishedFiltration
open Polynomial
open scoped BigOperators Polynomial
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section

variable {I V : Type*} [Fintype I] [DecidableEq I]

abbrev Polys (V I : Type*) := V × Mask I → ℚ[X]

def multiplyBy (p : ℚ[X]) : ℚ[X] →ₗ[ℚ] ℚ[X] where
  toFun q := p*q
  map_add' a b := mul_add p a b
  map_smul' c q := by simp

theorem multiplyBy_apply (p q : ℚ[X]) : multiplyBy p q = p*q := rfl

def slotSpace (nodes : I → ℚ) (s : Mask I) (n : ℕ) : Submodule ℚ ℚ[X] :=
  degreeLT ℚ n ⊓ LinearMap.range (multiplyBy (rootProduct nodes s))

/-- Scalar coordinates are in the actual basis `publishedBasisEquiv` at
each v. The ambient space includes arbitrary polynomials. -/
def Hlt (nodes : I → ℚ) (n : ℕ) : Submodule ℚ (Polys V I) :=
  Submodule.pi Set.univ (fun a : V × Mask I => slotSpace nodes a.2 n)

abbrev H (nodes : I → ℚ) (j : ℕ) : Submodule ℚ (Polys V I) := Hlt nodes (j+1)

theorem mem_slotSpace (nodes : I → ℚ) (s : Mask I) (n : ℕ) (p : ℚ[X]) :
    p ∈ slotSpace nodes s n ↔ p.degree < n ∧ rootProduct nodes s ∣ p := by
  constructor
  · rintro ⟨hd,hr⟩
    obtain ⟨q,hq⟩ := LinearMap.mem_range.mp hr
    exact ⟨mem_degreeLT.mp hd,⟨q,hq.symm⟩⟩
  · rintro ⟨hd,q,hq⟩
    exact ⟨mem_degreeLT.mpr hd,LinearMap.mem_range.mpr ⟨q,hq.symm⟩⟩

theorem mem_Hlt (nodes : I → ℚ) (n : ℕ) (h : Polys V I) :
    h ∈ Hlt nodes n ↔ ∀ v s, (h (v,s)).degree < n ∧ rootProduct nodes s ∣ h (v,s) := by
  simp only [Hlt, Submodule.mem_pi, Set.mem_univ, true_implies, mem_slotSpace, Prod.forall]

theorem Hlt_zero (nodes : I → ℚ) : Hlt (V:=V) nodes 0 = ⊥ := by
  ext h
  rw [Submodule.mem_bot]
  constructor
  · intro hh
    funext a
    have d := ((mem_Hlt nodes 0 h).1 hh a.1 a.2).1
    by_contra e
    rw [degree_eq_natDegree e, Nat.cast_lt] at d
    omega
  · rintro rfl
    exact (Hlt nodes 0).zero_mem

theorem root_mul_degree_lt_iff
    (nodes : I → ℚ) (s : Mask I) (n : ℕ) (q : ℚ[X]) :
    rootProduct nodes s * q ∈ degreeLT ℚ n ↔ q ∈ degreeLT ℚ (n-weight s) := by
  by_cases hq : q = 0
  · simp [hq]
  have hp : rootProduct nodes s ≠ 0 := (rootProduct_monic nodes s).ne_zero
  rw [mem_degreeLT, mem_degreeLT, degree_eq_natDegree (mul_ne_zero hp hq),
    degree_eq_natDegree hq, natDegree_mul hp hq, rootProduct_degree, Nat.cast_lt, Nat.cast_lt]
  omega

/-- An exact coordinate equivalence, including degree budgets below
the number of roots (the corresponding coordinate is then zero). -/
def slotSpaceEquiv (nodes : I → ℚ) (s : Mask I) (n : ℕ) :
    degreeLT ℚ (n-weight s) ≃ₗ[ℚ] slotSpace nodes s n := by
  let L : degreeLT ℚ (n-weight s) →ₗ[ℚ] slotSpace nodes s n :=
    ((multiplyBy (rootProduct nodes s)).comp (degreeLT ℚ (n-weight s)).subtype).codRestrict
      (slotSpace nodes s n) (fun q =>
        (mem_slotSpace nodes s n (rootProduct nodes s * q.val)).2
          ⟨mem_degreeLT.mp ((root_mul_degree_lt_iff nodes s n q.val).2 q.property), dvd_mul_right _ _⟩)
  refine LinearEquiv.ofBijective L ⟨?_,?_⟩
  · intro q₁ q₂ e
    apply Subtype.ext
    have u : rootProduct nodes s * q₁.val = rootProduct nodes s * q₂.val :=
      congrArg Subtype.val e
    exact mul_left_cancel₀ (rootProduct_monic nodes s).ne_zero u
  · intro p
    obtain ⟨hdegree,q,e⟩ := (mem_slotSpace nodes s n p.val).1 p.property
    have b : rootProduct nodes s * q ∈ degreeLT ℚ n := by
      rw [← e]
      exact mem_degreeLT.mpr hdegree
    refine ⟨⟨q,(root_mul_degree_lt_iff nodes s n q).1 b⟩,?_⟩
    exact Subtype.ext e.symm

def coordinatewise (nodes : I → ℚ) (n : ℕ) :
    Hlt (V:=V) nodes n ≃ₗ[ℚ] ((a : V × Mask I) → slotSpace nodes a.2 n) where
  toFun h a := ⟨h.val a, (Submodule.mem_pi.mp h.property) a (Set.mem_univ a)⟩
  invFun a := ⟨fun x => (a x).val, Submodule.mem_pi.mpr (fun x _ => (a x).property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def filtrationCoordinates (nodes : I → ℚ) (n : ℕ) :
    Hlt (V:=V) nodes n ≃ₗ[ℚ] ((a : V × Mask I) → Fin (n-weight a.2) → ℚ) :=
  (coordinatewise nodes n).trans (LinearEquiv.piCongrRight (fun a =>
    (slotSpaceEquiv nodes a.2 n).symm.trans (degreeLTEquiv ℚ (n-weight a.2))))

variable [Fintype V]

instance HltFinite (nodes : I → ℚ) (n : ℕ) : FiniteDimensional ℚ (Hlt (V:=V) nodes n) :=
  FiniteDimensional.of_injective (filtrationCoordinates (V:=V) nodes n).toLinearMap
    (filtrationCoordinates (V:=V) nodes n).injective

theorem Hlt_finrank (nodes : I → ℚ) (n : ℕ) :
    Module.finrank ℚ (Hlt (V:=V) nodes n) = ∑ a : V × Mask I, (n-weight a.2) := by
  rw [(filtrationCoordinates (V:=V) nodes n).finrank_eq, Module.finrank_pi_fintype]
  simp

/-- The paper's exact count of newly available v,S coordinates at order j. -/
theorem Hlt_dim_increment (nodes : I → ℚ) (j : ℕ) :
    Module.finrank ℚ (H (V:=V) nodes j) =
      Module.finrank ℚ (Hlt (V:=V) nodes j) +
        (Finset.univ.filter (fun a : V × Mask I => weight a.2 ≤ j)).card := by
  classical
  simp only [H, Hlt_finrank]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : weight a.2 ≤ j <;> simp only [ha, if_true, if_false] <;> omega

#print axioms mem_Hlt
#print axioms Hlt_zero
#print axioms root_mul_degree_lt_iff
#print axioms filtrationCoordinates
#print axioms Hlt_finrank
#print axioms Hlt_dim_increment
end
end Reconstruction.LayoutMismatch.PublishedFiltration

