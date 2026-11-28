import LayoutBudget
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

open scoped BigOperators Polynomial
open Matrix Polynomial

namespace Reconstruction.VisitRuntime

open LayoutBudget (GroupFiber restrictGroupMatrix measurementRank)

noncomputable section

private def bit (b : Bool) : ℚ := if b then 1 else 0

private theorem bit_injective : Function.Injective bit := by
  intro x y h
  cases x <;> cases y <;> simp_all [bit]

/-- One physical measurement matrix on Boolean group assignments. -/
def groupImage {M V : Type*} [Fintype V] (C : Matrix M V ℚ) :=
  Set.range (fun x : V → Bool => C.mulVec (fun v => bit (x v)))

noncomputable instance {M V : Type*} [Fintype V] (C : Matrix M V ℚ) :
    Fintype (groupImage C) := (Set.finite_range _).fintype

/-- Independent columns produce distinct Boolean subset sums. -/
theorem groupImage_card_ge {M V : Type*} [Fintype M] [Fintype V] (C : Matrix M V ℚ) :
    2 ^ C.rank ≤ Fintype.card (groupImage C) := by
  classical
  have hcols : ∃ f : Fin C.rank → M → ℚ, (∀ i, f i ∈ Set.range C.col) ∧ LinearIndependent ℚ f := by
    rw [Matrix.rank_eq_finrank_span_cols]
    obtain ⟨f, hf, _, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range C.col)
    exact ⟨f, hf, hli⟩
  obtain ⟨f, hf, hli⟩ := hcols
  choose e he using hf
  have hei : Function.Injective e := by
    intro i j hij
    apply hli.injective
    rw [← he i, ← he j, hij]
  let bsum (x : Fin C.rank → Bool) : M → ℚ := ∑ i, bit (x i) • f i
  have hsum (x : Fin C.rank → Bool) : bsum x ∈ groupImage C := by
    let y := Function.extend e x (fun _ => false)
    refine ⟨y, ?_⟩
    ext m
    simp only [Matrix.mulVec, dotProduct, bsum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e))]
    · rw [Finset.sum_image (fun i _ j _ h => hei h)]
      apply Finset.sum_congr rfl
      intro i _
      rw [show y (e i) = x i from hei.extend_apply _ _ _, ← he i, Matrix.col_apply, mul_comm]
    · intro j _ hj
      have hnot : ¬ ∃ i, e i = j := by simpa using hj
      simp [y, Function.extend_apply' _ _ _ hnot, bit]
  have hinj : Function.Injective bsum := by
    intro x y h
    have hz : ∑ i, (bit (x i) - bit (y i)) • f i = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr h
    have hz' := (linearIndependent_iff'.mp hli) Finset.univ _ hz
    funext i
    exact bit_injective (sub_eq_zero.mp (hz' i (Finset.mem_univ i)))
  simpa only [Fintype.card_pi_const, Fintype.card_bool] using
    Fintype.card_le_of_embedding (Function.Embedding.mk (fun x => ⟨bsum x, hsum x⟩)
      (fun _ _ h => hinj (congrArg Subtype.val h)))

/-- The jointly Boolean-reachable tuples, with one component per source group. -/
def reachableImage {V G : Type*} (a : V → G) [∀ g, Fintype (GroupFiber a g)]
    {M : G → Type*} (C : ∀ g, Matrix (M g) (GroupFiber a g) ℚ) :=
  Set.range (fun x : V → Bool => fun g => (C g).mulVec (fun v => bit (x v.val)))

noncomputable instance {V G : Type*} [Fintype V] (a : V → G)
    [∀ g, Fintype (GroupFiber a g)] {M : G → Type*}
    (C : ∀ g, Matrix (M g) (GroupFiber a g) ℚ) : Fintype (reachableImage a C) :=
  (Set.finite_range _).fintype

/-- Equation (2)'s restricted measurement rank gives this many reachable tuples.
The construction extends the selected Boolean assignment by zero. -/
theorem reachableImage_card_ge {V U G : Type*} [Fintype V] [Fintype U]
    [Fintype G] [DecidableEq G] (ι : U ↪ V) (a : V → G) {M : G → Type*}
    [∀ g, Fintype (M g)] (C : ∀ g, Matrix (M g) (GroupFiber a g) ℚ) :
    2 ^ measurementRank ι a C ≤ Fintype.card (reachableImage a C) := by
  classical
  let B := fun g => restrictGroupMatrix ι a g (C g)
  have hmem (y : ∀ g, groupImage (B g)) : (fun g => (y g).val) ∈ reachableImage a C := by
    choose x hx using (fun g => (y g).property)
    let z (u : U) := x (a (ι u)) ⟨u, rfl⟩
    refine ⟨Function.extend ι z (fun _ => false), ?_⟩
    funext g m
    rw [← hx g]
    let e : GroupFiber (a ∘ ι) g ↪ GroupFiber a g :=
      ⟨fun u => ⟨ι u.val, u.property⟩, fun _ _ h => Subtype.ext (ι.injective (congrArg Subtype.val h))⟩
    simp only [Matrix.mulVec, dotProduct]
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e))]
    · rw [Finset.sum_image (fun i _ j _ h => e.injective h)]
      apply Finset.sum_congr rfl
      intro u _
      change _ * bit (Function.extend ι z (fun _ => false) (ι u.val)) = _
      rw [ι.injective.extend_apply]
      have hz (v : U) (g' : G) (h : a (ι v) = g') : z v = x g' ⟨v, h⟩ := by
        subst g'
        rfl
      rw [hz u.val g u.property]
      rfl
    · intro v _ hv
      have hv' : ¬ ∃ u, ι u = v.val := by
        rintro ⟨u, hu⟩
        apply hv
        refine Finset.mem_image.mpr ⟨⟨u, by simpa only [Function.comp_apply, hu] using v.property⟩,
          Finset.mem_univ _, Subtype.ext hu⟩
      simp [Function.extend_apply' _ _ _ hv', bit]
  let E : (∀ g, groupImage (B g)) ↪ reachableImage a C :=
    ⟨fun y => ⟨_, hmem y⟩, fun _ _ h => funext fun g => Subtype.ext (congrFun (congrArg Subtype.val h) g)⟩
  have hcard := Fintype.card_le_of_embedding E
  rw [Fintype.card_pi] at hcard
  rw [measurementRank, ← Finset.prod_pow_eq_pow_sum]
  exact (Finset.prod_le_prod' (fun g _ => groupImage_card_ge (B g))).trans hcard

/-- The incidence model of Section 2, with arbitrary rational measurements. -/
structure PhysicalLayout (V Factor : Type*) [DecidableEq V] (Q r R : ℕ) where
  node : Fin Q → ℚ
  nodes_injective : Function.Injective node
  nodes_ne_zero : ∀ t, node t ≠ 0
  source : Fin Q → V → Fin r
  target : Fin Q → Factor → Fin r
  scope : Factor → V → Prop
  rows : Fin Q → Fin r → ℕ
  measure : ∀ t g, Matrix (Fin (rows t g)) (GroupFiber (source t) g) ℚ
  poly : Factor → V → V → ℚ[X]
  constant : ∀ f v, scope f v → ∀ w, (poly f v w).eval 0 = if v = w then 1 else 0
  degree : ∀ f v, scope f v → ∀ w, (poly f v w).natDegree ≤ R
  foreign : ∀ t f v, scope f v → ∀ g, target t f ≠ g →
    (fun w : GroupFiber (source t) g => (poly f v w.val).eval (node t)) ∈
      Submodule.span ℚ (Set.range (measure t g).row)

variable {V Factor : Type*} [Fintype V] [DecidableEq V] {Q r R : ℕ}

namespace PhysicalLayout

def groupSize (L : PhysicalLayout V Factor Q r R) (t : Fin Q) (g : Fin r) : ℕ :=
  Fintype.card (GroupFiber (L.source t) g)

def balanced (L : PhysicalLayout V Factor Q r R) : Prop :=
  ∀ t g, (L.groupSize t g:ℝ) ≤ 2*(Fintype.card V:ℝ)/(r:ℝ)

def rankOn (L : PhysicalLayout V Factor Q r R) (U : Finset V) (t : Fin Q) : ℕ :=
  measurementRank (Subtype.val : U → V) (L.source t) (L.measure t)

theorem sum_groupSize (L : PhysicalLayout V Factor Q r R) (t : Fin Q) :
    ∑ g, L.groupSize t g = Fintype.card V := by
  unfold groupSize
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv (L.source t))

end PhysicalLayout

def taylorCutoff (N Q R d₀ : ℕ) : ℕ := min N (d₀*R/Q)

/-- Distinct visits of the indicated index set into the elementary visit record.
The two existential scan/visit nodes do not have to coincide. -/
structure Visits (L : PhysicalLayout V Factor Q r R) (d₀ T : ℕ) where
  measurement : ∀ t, reachableImage (L.source t) (L.measure t) ↪ Fin T
  taylorNode : Fin Q
  taylor : {U : Finset V // U.card ≤ taylorCutoff (Fintype.card V) Q R d₀} ↪ Fin T
  scanNode : Fin Q
  scanGroup : Fin r
  largest : ∀ g, L.groupSize scanNode g ≤ L.groupSize scanNode scanGroup
  scan : (GroupFiber (L.source scanNode) scanGroup → Bool) ↪ Fin T

/-- The extra scan assumption in the unbalanced Section 6 variant. -/
def ScansAtEveryNode (L : PhysicalLayout V Factor Q r R) (T : ℕ) : Prop :=
  ∀ t, ∃ g, (∀ g', L.groupSize t g' ≤ L.groupSize t g) ∧
    Nonempty ((GroupFiber (L.source t) g → Bool) ↪ Fin T)

namespace Visits

variable {L : PhysicalLayout V Factor Q r R} {d₀ T : ℕ} (W : Visits L d₀ T)

include W

theorem nodes_pos : 0 < Q := Nat.zero_lt_of_lt W.taylorNode.isLt

theorem groups_pos : 0 < r := Nat.zero_lt_of_lt W.scanGroup.isLt

theorem visits_pos : 0 < T := Nat.zero_lt_of_lt (W.scan (fun _ => false)).isLt

/-- Cost of visiting reachable tuples, also when only the indicated variables vary. -/
theorem rank_pow_le (U : Finset V) (t : Fin Q) : 2^(L.rankOn U t) ≤ T :=
  (reachableImage_card_ge (Function.Embedding.subtype (· ∈ U)) (L.source t) (L.measure t)).trans
    (by simpa only [Fintype.card_fin] using Fintype.card_le_of_embedding (W.measurement t))

omit W [DecidableEq V] in
private theorem card_taylor_subsets (s : ℕ) : Fintype.card {U : Finset V // U.card ≤ s} =
    ∑ j ∈ Finset.range (s+1), (Fintype.card V).choose j := by
  classical
  rw [Fintype.card_subtype]
  have hx := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ.powerset : Finset (Finset V)) (Finset.range (s+1)) Finset.card
  simp only [Finset.mem_range, Nat.lt_succ_iff, Finset.powerset_univ] at hx
  rw [← hx]
  apply Finset.sum_congr rfl
  intro j _
  have he : Finset.univ.filter (fun U : Finset V => U.card = j) = Finset.univ.powersetCard j := by
    ext
    simp [Finset.mem_powersetCard]
  rw [he, Finset.card_powersetCard, Finset.card_univ]

theorem taylor_sum_le :
    ∑ j ∈ Finset.range (taylorCutoff (Fintype.card V) Q R d₀+1), (Fintype.card V).choose j ≤ T := by
  simpa only [card_taylor_subsets, Fintype.card_fin] using Fintype.card_le_of_embedding W.taylor

theorem taylor_choose_le {s : ℕ} (hs : s ≤ taylorCutoff (Fintype.card V) Q R d₀) :
    (Fintype.card V).choose s ≤ T := by
  apply le_trans ?_ W.taylor_sum_le
  exact Finset.single_le_sum (fun j _ => Nat.zero_le ((Fintype.card V).choose j))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hs))

theorem taylor_pow_le {s : ℕ} (hs : s ≤ taylorCutoff (Fintype.card V) Q R d₀) : 2^s ≤ T := by
  classical
  have hN : s ≤ Fintype.card V := hs.trans (min_le_left ..)
  obtain ⟨U, _, hU⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset V))
    (by simpa only [Finset.card_univ] using hN)
  let e : (U.powerset : Finset (Finset V)) ↪ {A : Finset V // A.card ≤ taylorCutoff (Fintype.card V) Q R d₀} :=
    ⟨fun A => ⟨A.val, (Finset.card_le_card (Finset.mem_powerset.mp A.property)).trans (hU.symm ▸ hs)⟩,
      fun _ _ h => Subtype.ext (congrArg (fun A : {A : Finset V // A.card ≤ taylorCutoff (Fintype.card V) Q R d₀} => A.val) h)⟩
  simpa only [Fintype.card_coe, Finset.card_powerset, hU, Fintype.card_fin] using
    Fintype.card_le_of_embedding (e.trans W.taylor)

theorem scan_pow_le : 2^(L.groupSize W.scanNode W.scanGroup) ≤ T := by
  simpa [PhysicalLayout.groupSize, Fintype.card_fun] using Fintype.card_le_of_embedding W.scan

theorem largest_size_ge : Fintype.card V ≤ r * L.groupSize W.scanNode W.scanGroup := by
  calc
    _ = ∑ g, L.groupSize W.scanNode g := (L.sum_groupSize W.scanNode).symm
    _ ≤ ∑ _ : Fin r, L.groupSize W.scanNode W.scanGroup := Finset.sum_le_sum (fun g _ => W.largest g)
    _ = _ := by simp

omit W in
theorem scan_pow_le_at_every_node (H : ScansAtEveryNode L T) (t : Fin Q) (g : Fin r) :
    2^(L.groupSize t g) ≤ T := by
  obtain ⟨g', hg', ⟨e⟩⟩ := H t
  refine (Nat.pow_le_pow_right (by decide) (hg' g)).trans ?_
  simpa [PhysicalLayout.groupSize, Fintype.card_fun] using Fintype.card_le_of_embedding e

end Visits

end

end Reconstruction.VisitRuntime
