import MainClonedCNF
import GroupProducts
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace S8

open scoped BigOperators
variable {V A B : Type*} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

def orValue (a b : Bool) : ℕ := if a || b then 1 else 0

omit [DecidableEq V] in
theorem pinned_count_product (E : Finset (V × V)) (σ : V → Bool) :
    PinnedCNF.modelCount (PinnedCNF.formula E σ) =
      ∏ e ∈ E, orValue (σ e.1) (σ e.2) := by
  rw [PinnedCNF.count_eq_edge_product]
  apply Finset.prod_congr rfl
  intro e _
  cases σ e.1 <;> cases σ e.2 <;> rfl

/-- A precomputed bucket with both endpoint indices typed in the particular
    symbol group. There is no access to sign positions outside the group. -/
noncomputable def bucket (E : Finset (V × V)) (label : V → A)
    (tied : ∀ e ∈ E, label e.1 = label e.2) (g : A) :
    List ({v // label v = g} × {v // label v = g}) :=
  ((E.filter fun e => label e.1 = g).attach.toList).map fun e =>
    let h := Finset.mem_filter.mp e.2
    (⟨e.1.1, h.2⟩, ⟨e.1.2, (tied e.1 h.1).symm.trans h.2⟩)

def scan {X : Type*} (edges : List (X × X)) (sign : X → Bool) : ℕ × ℕ :=
  edges.foldr (fun e r => (orValue (sign e.1) (sign e.2) * r.1, r.2 + 5)) (1, 0)

theorem scan_value {X : Type*} (edges : List (X × X)) (sign : X → Bool) :
    (scan edges sign).1 = (edges.map fun e => orValue (sign e.1) (sign e.2)).prod := by
  induction edges with
  | nil => rfl
  | cons e es ih => simp [scan, ← ih]

theorem scan_work {X : Type*} (edges : List (X × X)) (sign : X → Bool) :
    (scan edges sign).2 = 5 * edges.length := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
    change (scan es sign).2 + 5 = _
    rw [ih, List.length_cons, Nat.mul_succ]

noncomputable def localFactor (E : Finset (V × V)) (label : V → A)
    (tied : ∀ e ∈ E, label e.1 = label e.2) (g : A) (sign : {v // label v = g} → Bool) : ℕ :=
  (scan (bucket E label tied g) sign).1

omit [Fintype V] [DecidableEq V] [Fintype A] in
theorem localFactor_value (E : Finset (V × V)) (label : V → A)
    (tied : ∀ e ∈ E, label e.1 = label e.2) (g : A) (σ : V → Bool) :
    localFactor E label tied g (fun v => σ v.1) =
      ∏ e ∈ E with label e.1 = g, orValue (σ e.1) (σ e.2) := by
  rw [localFactor, scan_value]
  simp only [bucket, List.map_map, Function.comp_def, Finset.prod_map_toList]
  exact Finset.prod_attach (E.filter fun e => label e.1 = g)
    (fun e : V × V => orValue (σ e.1) (σ e.2))

theorem route_product (E : Finset (V × V)) (label : V → A)
    (tied : ∀ e ∈ E, label e.1 = label e.2) (σ : V → Bool) :
    (∏ g, localFactor E label tied g (fun v => σ v.1)) =
      ∏ e ∈ E, orValue (σ e.1) (σ e.2) := by
  simp only [localFactor_value]
  exact Finset.prod_fiberwise_of_maps_to (t := Finset.univ) (g := fun e : V × V => label e.1) (fun _ _ => Finset.mem_univ _)
    (fun e => orValue (σ e.1) (σ e.2))

/-- One cross-route multiplication at the arbitrary local-function interface,
    on the actual three-occurrence cloned CNF. -/
theorem cross_route_count (internal exterior : Finset (V × V))
    (disjoint : Disjoint internal exterior)
    (left right : (internal ∪ exterior : Finset _) → Fin 4)
    (main : V → A) (appD : V → B)
    (mainTied : ∀ e ∈ internal, main e.1 = main e.2)
    (appTied : ∀ e ∈ exterior, appD e.1 = appD e.2)
    (σ : V → Bool) :
    PinnedCNF.modelCount (MainClonedCNF.formula (internal ∪ exterior) left right σ) =
      (∏ g, localFactor internal main mainTied g (fun v => σ v.1)) *
      (∏ h, localFactor exterior appD appTied h (fun v => σ v.1)) := by
  rw [MainClonedCNF.modelCount_cloned, pinned_count_product, Finset.prod_union disjoint,
    route_product, route_product]

/-- Indexed work after storing the buckets, including four operations per
    symbol (bucket/loop overhead and accumulate) and one final multiply. -/
noncomputable def indexedWork (E : Finset (V × V)) (label : V → A)
    (tied : ∀ e ∈ E, label e.1 = label e.2) (σ : V → Bool) : ℕ :=
  ∑ g, ((scan (bucket E label tied g) (fun v => σ v.1)).2 + 4)

theorem indexedWork_eq (E : Finset (V × V)) (label : V → A)
    (tied : ∀ e ∈ E, label e.1 = label e.2) (σ : V → Bool) :
    indexedWork E label tied σ = 5 * E.card + 4 * Fintype.card A := by
  simp only [indexedWork, scan_work, bucket, List.length_map, Finset.length_toList,
    Finset.card_attach, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  change 5 * (∑ g, (E.filter fun e => label e.1 = g).card) + Fintype.card A * 4 = _
  rw [Nat.mul_comm (Fintype.card A) 4]
  congr 1
  apply congrArg (5 * ·)
  simp only [Finset.card_eq_sum_ones]
  exact Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (g := fun e : V × V => label e.1) (fun _ _ => Finset.mem_univ _)
    (fun _ => 1)

theorem cross_route_indexed_bound (internal exterior : Finset (V × V))
    (disjoint : Disjoint internal exterior)
    (regular : ∀ v, GraphCutMoments.degree (internal ∪ exterior) v = 3)
    (main : V → A) (appD : V → B) (mainTied : ∀ e ∈ internal, main e.1 = main e.2)
    (appTied : ∀ e ∈ exterior, appD e.1 = appD e.2) (σ : V → Bool)
    (hMain : Fintype.card A ≤ Fintype.card V) (hD : Fintype.card B = 64)
    (hV : 1 ≤ Fintype.card V) :
    indexedWork internal main mainTied σ + indexedWork exterior appD appTied σ + 1 ≤
      269 * Fintype.card V := by
  have h := GraphCutMoments.regular_edge_count _ 3 regular
  rw [Finset.card_union_of_disjoint disjoint] at h
  rw [indexedWork_eq, indexedWork_eq, hD]
  omega

#print axioms pinned_count_product
#print axioms route_product
#print axioms cross_route_count
#print axioms scan_work
#print axioms indexedWork_eq
#print axioms cross_route_indexed_bound

end S8

