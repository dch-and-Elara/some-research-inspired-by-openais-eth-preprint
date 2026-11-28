import P2PublishedFiltrationIncrement
import LayoutMismatchCount

/-! Section 4, equation (7), now also verified with the printed filtration
proof. The incidence-to-selected-axis bridge uses the published input model. -/
namespace Reconstruction.LayoutMismatch.PublishedFiltration
open Polynomial Matrix
open LayoutBudget (GroupFiber)
open scoped Polynomial
set_option autoImplicit false
set_option warningAsError true
noncomputable section

/-- Equation (7), proved by telescoping the printed filtration, rather
than by the independent slot-kernel packing proof in the base project. -/
theorem mismatch_rank_selected_via_filtration {I V G : Type*}
    [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G]
    {M : I → G → Type*} [∀ t g, Fintype (M t g)]
    (nodes : I → ℚ) (a b : I → V → G)
    (C : ∀ t g, Matrix (M t g) (GroupFiber (a t) g) ℚ)
    (P : Matrix V V ℚ[X]) (R : ℕ)
    (hnodes : Function.Injective nodes) (hnonzero : ∀ t, nodes t ≠ 0)
    (hR : R < Fintype.card I)
    (hzero : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0)
    (hdegree : ∀ u v, (P u v).natDegree ≤ R)
    (hforeign : ∀ t u g, b t u ≠ g →
      (fun v : GroupFiber (a t) g => (P u v.val).eval (nodes t)) ∈
        Submodule.span ℚ (Set.range (C t g).row)) :
    2 * (∑ v, phi R (mismatchCount (layoutWord a b v))) ≤
      ((∑ t, ∑ g, (C t g).rank : ℕ) : ℚ) := by
  have hbound := displayed_filtration_mismatch_budget nodes a b C P R hnodes hnonzero
    hzero hdegree hforeign hR
  have hk : Fintype.card I ≠ 0 := by omega
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero hk
  have hdiv : 2^Fintype.card I / 2 = 2^(Fintype.card I-1) := by
    rw [hn,pow_succ]
    simp
  rw [hdiv,Fintype.sum_prod_type] at hbound
  have hrat :
      ((∑ v, ∑ s : Mask I,
        (Fintype.card I-R-weight s-weight (dualMask (layoutWord a b v) s)) : ℕ) : ℚ) ≤
      (2 : ℚ)^(Fintype.card I-1)*((∑ t, ∑ g, (C t g).rank : ℕ) : ℚ) := by
    exact_mod_cast hbound
  rw [Nat.cast_sum] at hrat
  simp only [weightedModeSum,← Finset.mul_sum] at hrat
  have hpow : (2 : ℚ)^Fintype.card I = (2 : ℚ)^(Fintype.card I-1)*2 := by
    rw [hn,pow_succ]
    simp
  rw [hpow,mul_assoc] at hrat
  exact le_of_mul_le_mul_left hrat (pow_pos (by decide) _)

theorem mismatch_rank_via_filtration {V I G Factor : Type*} [DecidableEq V]
    [Fintype G] [DecidableEq G] {M : I → G → Type*} [∀ t g, Fintype (M t g)]
    (V₀ : Finset V) (T : Finset I) (node : I → ℚ) (R : ℕ)
    (a : I → V → G) (b : I → Factor → G) (scope : Factor → V → Prop)
    (chosen : V₀ → Factor) (hchosen : ∀ v : V₀, scope (chosen v) v.val)
    (P : Factor → V → V → ℚ[X])
    (C : ∀ t g, Matrix (M t g) (GroupFiber (a t) g) ℚ)
    (hnodes : Set.InjOn node (↑T : Set I)) (hnonzero : ∀ t ∈ T, node t ≠ 0)
    (hR : R < T.card)
    (hzero : ∀ f v, scope f v → ∀ w, (P f v w).eval 0 = if v = w then 1 else 0)
    (hdegree : ∀ f v, scope f v → ∀ w, (P f v w).natDegree ≤ R)
    (hforeign : ∀ t ∈ T, ∀ f v, scope f v → ∀ g, b t f ≠ g →
      (fun w : GroupFiber (a t) g => (P f v w.val).eval (node t)) ∈
        Submodule.span ℚ (Set.range (C t g).row)) :
    2 * (∑ v : V₀, phi R (T.filter (fun t => a t v.val ≠ b t (chosen v))).card) ≤
      ((∑ t : T, LayoutBudget.measurementRank (fun v : V₀ => v.val) (a t) (C t) : ℕ) : ℚ) := by
  classical
  let src (t : T) (v : V₀) := a t.val v.val
  let tgt (t : T) (v : V₀) := b t.val (chosen v)
  let C' (t : T) (g : G) : Matrix (M t.val g) (GroupFiber (src t) g) ℚ :=
    LayoutBudget.restrictGroupMatrix (fun v : V₀ => v.val) (a t.val) g (C t.val g)
  let A : Matrix V₀ V₀ ℚ[X] := Matrix.of (fun u v => P (chosen u) u.val v.val)
  have hA0 (u v : V₀) : (A u v).eval 0 = if u = v then 1 else 0 := by
    change (P (chosen u) u.val v.val).eval 0 = _
    simpa only [Subtype.ext_iff] using hzero (chosen u) u.val (hchosen u) v.val
  have hspan (t : T) (u : V₀) (g : G) (h : tgt t u ≠ g) :
      (fun v : GroupFiber (src t) g => (A u v.val).eval (node t.val)) ∈
        Submodule.span ℚ (Set.range (C' t g).row) := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp
      (hforeign t.val t.property (chosen u) u.val (hchosen u) g h)
    apply (Submodule.mem_span_range_iff_exists_fun ℚ).mpr
    refine ⟨c, ?_⟩
    funext v
    simpa only [Finset.sum_apply, Pi.smul_apply, Matrix.row_apply, C', A,
      LayoutBudget.restrictGroupMatrix, Matrix.submatrix_apply, Matrix.of_apply, id_eq] using
        congrFun hc (⟨v.val.val, v.property⟩ : GroupFiber (a t.val) g)
  have hcount (v : V₀) :
      mismatchCount (layoutWord src tgt v) =
        (T.filter (fun t => a t v.val ≠ b t (chosen v))).card := by
    rw [mismatchCount, ← Fintype.card_coe]
    let e : Active (layoutWord src tgt v) ≃ ↥(T.filter (fun t => a t v.val ≠ b t (chosen v))) :=
      { toFun := fun i => ⟨i.val.val, Finset.mem_filter.mpr
          ⟨i.val.property, fun h => i.property (congrArg groupSlope h)⟩⟩
        invFun := fun i => ⟨⟨i.val, (Finset.mem_filter.mp i.property).1⟩,
          fun h => (Finset.mem_filter.mp i.property).2 (groupSlope_injective h)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Fintype.card_congr e
  have h := mismatch_rank_selected_via_filtration (fun t : T => node t.val) src tgt C' A R
    (fun u v h => Subtype.ext (hnodes u.property v.property h))
    (fun t => hnonzero t.val t.property)
    (by simpa only [Fintype.card_coe] using hR) hA0
    (fun u v => hdegree (chosen u) u.val (hchosen u) v.val) hspan
  simpa only [hcount, C', LayoutBudget.measurementRank] using h

#print axioms mismatch_rank_selected_via_filtration
#print axioms mismatch_rank_via_filtration
end
end Reconstruction.LayoutMismatch.PublishedFiltration

