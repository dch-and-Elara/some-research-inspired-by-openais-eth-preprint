import P2PublishedFiltrationOrigin
import P2PublishedFiltrationTest

/-! The dimension-increment proof after printed Eq. (9). This works
directly in the literal polynomial filtration. -/
namespace Reconstruction.LayoutMismatch.PublishedFiltration
open Polynomial
open LayoutBudget (GroupFiber)
open scoped BigOperators Polynomial
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section

variable {I V G : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
  [Fintype G] [DecidableEq G]
variable (node : I → ℚ) (a b : I → V → G)
variable {Rows : I → G → Type*} [∀ t g, Fintype (Rows t g)]
variable (Cmat : ∀ t g, Matrix (Rows t g) (GroupFiber (a t) g) ℚ)

def availableOriginCoordinates (j : ℕ) : Finset (V × Mask I) :=
  Finset.univ.filter (fun x => weight x.2 ≤ j)

def deletedOriginCoordinates (R j : ℕ) : Finset (V × Mask I) :=
  (availableOriginCoordinates (V:=V) (I:=I) j).filter (fun x =>
    R+j+weight (dualMask (layoutWord a b x.1) x.2) < Fintype.card I)

theorem beyond_degree_origin_zero (j : ℕ) {h : Polys V I} (hh : h ∈ H node j)
    (x : V × Mask I) (large : j < weight x.2) : (h x).eval 0 = 0 := by
  obtain ⟨d,q,eq⟩ := (mem_Hlt node (j+1) h).1 hh x.1 x.2
  change h x = rootProduct node x.2 * q at eq
  have p : h x ∈ degreeLT ℚ (j+1) := mem_degreeLT.mpr d
  rw [eq] at p
  have ql := (root_mul_degree_lt_iff node x.2 (j+1) q).1 p
  have zero : j+1-weight x.2 = 0 := by omega
  rw [zero] at ql
  have qe : q = 0 := by
    by_contra hne
    have deg := mem_degreeLT.mp ql
    rw [degree_eq_natDegree hne,Nat.cast_lt] at deg
    omega
  rw [eq,qe,mul_zero,eval_zero]

variable (P : Matrix V V ℚ[X]) (R : ℕ)
variable (inj : Function.Injective node) (nonzero : ∀ i, node i ≠ 0)
variable (h0 : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0)
variable (degree : ∀ u v, (P u v).natDegree ≤ R)
variable (foreign : ∀ t u g, b t u ≠ g →
      (fun v : GroupFiber (a t) g => (P u v.val).eval (node t)) ∈
        Submodule.span ℚ (Set.range (Cmat t g).row))

include inj nonzero h0 degree foreign in
theorem origin_increment_count (j : ℕ) :
    Module.finrank ℚ (Ilt node a b Cmat (j+1)) -
      Module.finrank ℚ (Ilt node a b Cmat j) ≤
    (availableOriginCoordinates (V:=V) (I:=I) j).card -
      (deletedOriginCoordinates a b R j).card := by
  classical
  let kept := availableOriginCoordinates (V:=V) (I:=I) j \ deletedOriginCoordinates a b R j
  let U := LinearMap.range (originValues node a b Cmat (j+1))
  have vanish (r : U) (x : V × Mask I) (outside : x ∉ kept) : r.val x = 0 := by
    obtain ⟨h,eq⟩ := r.property
    rw [← eq]
    change (h.val x).eval 0 = 0
    by_cases fits : weight x.2 ≤ j
    · have hd : x ∈ deletedOriginCoordinates a b R j := by
        by_contra hn
        exact outside (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,fits⟩,hn⟩)
      exact forced_origin_coordinate_zero node a b Cmat P R j inj nonzero h0 degree foreign
        h x.1 x.2 (Finset.mem_filter.mp hd).2
    · exact beyond_degree_origin_zero node j ((mem_Ilt node a b Cmat (j+1) h.val).1 h.property).1
        x (Nat.lt_of_not_ge fits)
  let L : U →ₗ[ℚ] ({x // x ∈ kept} → ℚ) :=
    { toFun r x := r.val x.val
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hi : Function.Injective L := by
    intro r s e
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ kept
    · exact congrFun e ⟨x,hx⟩
    · rw [vanish r x hx,vanish s x hx]
  have d := LinearMap.finrank_le_finrank_of_injective hi
  rw [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] at d
  rw [origin_dim_increment node a b Cmat j nonzero]
  have kept_card : kept.card = (availableOriginCoordinates (V:=V) (I:=I) j).card -
      (deletedOriginCoordinates a b R j).card :=
    Finset.card_sdiff_of_subset (show deletedOriginCoordinates a b R j ⊆
      availableOriginCoordinates (V:=V) (I:=I) j from Finset.filter_subset _ _)
  rw [kept_card] at d
  exact d

include inj nonzero h0 degree foreign in
theorem finite_codimension_lower_by_deleted (n : ℕ) :
    (∑ j ∈ Finset.range n, (deletedOriginCoordinates a b R j).card) ≤
      Module.finrank ℚ (Hlt (V:=V) node n) -
        Module.finrank ℚ (Ilt node a b Cmat n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hle : Module.finrank ℚ (Ilt node a b Cmat n) ≤
        Module.finrank ℚ (Hlt (V:=V) node n) :=
      Submodule.finrank_mono (show Ilt node a b Cmat n ≤ Hlt node n from inf_le_left)
    have dd : (deletedOriginCoordinates a b R n).card ≤
        (availableOriginCoordinates (V:=V) (I:=I) n).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have h := Hlt_dim_increment (V:=V) node n
    have e := origin_increment_count node a b Cmat P R inj nonzero h0 degree foreign n
    change Module.finrank ℚ (Hlt (V:=V) node (n+1)) = Module.finrank ℚ (Hlt (V:=V) node n) +
      (availableOriginCoordinates (V:=V) (I:=I) n).card at h
    omega

theorem sum_deleted_is_literal_budget :
    (∑ j ∈ Finset.range (Fintype.card I-R), (deletedOriginCoordinates a b R j).card) =
      ∑ x : V × Mask I, (Fintype.card I-R-weight x.2-weight (dualMask (layoutWord a b x.1) x.2)) := by
  classical
  simp only [deletedOriginCoordinates,availableOriginCoordinates,Finset.filter_filter,
    Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.sum_filter,← Finset.card_eq_sum_ones]
  have rangeEq :
      (Finset.range (Fintype.card I-R)).filter (fun j =>
        weight x.2 ≤ j ∧ R+j+weight (dualMask (layoutWord a b x.1) x.2) < Fintype.card I) =
      Finset.Ico (weight x.2) (Fintype.card I-R-weight (dualMask (layoutWord a b x.1) x.2)) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
    omega
  rw [rangeEq,Nat.card_Ico]
  omega

include inj nonzero h0 degree foreign in
/-- The displayed scalar sum immediately following the printed
filtration argument, obtained by telescoping its own dimension bounds. -/
theorem displayed_filtration_mismatch_budget (hR : R < Fintype.card I) :
    (∑ x : V × Mask I,
      (Fintype.card I-R-weight x.2-weight (dualMask (layoutWord a b x.1) x.2))) ≤
        (2^Fintype.card I / 2)*(∑ t, ∑ g, (Cmat t g).rank) := by
  rw [← sum_deleted_is_literal_budget a b R]
  apply (finite_codimension_lower_by_deleted node a b Cmat P R inj nonzero h0 degree foreign _).trans
  have hk : Fintype.card I ≠ 0 := by omega
  have e : 2^Fintype.card I / 2 = 2^(Fintype.card I-1) := by
    obtain ⟨k,h⟩ := Nat.exists_eq_succ_of_ne_zero hk
    rw [h,pow_succ]
    simp
  rw [e]
  exact nodal_kernel_codimension node a b Cmat _

#print axioms beyond_degree_origin_zero
#print axioms origin_increment_count
#print axioms finite_codimension_lower_by_deleted
#print axioms sum_deleted_is_literal_budget
#print axioms displayed_filtration_mismatch_budget
end
end Reconstruction.LayoutMismatch.PublishedFiltration

