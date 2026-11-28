import J6OrientedLayerSplit
import Mathlib.Tactic

/-! Exact full finite sum over the planted layer blocks, including
both sets of unmatched boundary layers. No disjointness of original
old table scopes inside a single copy is needed. -/
namespace J6OrientedLayerProduct
open scoped BigOperators
open J6OrientedLayerSplit
variable {R Y X : Type*} [CommRing R] [Fintype Y] [Fintype X]

def value (A : Y → R) (B : X → R) (F : Y → Option X → R)
    (L t : ℕ) (ht : t ≤ L) (d : (Fin L → Y) × (Fin L → X)) : R :=
  (∏ j, A (d.1 j)) * (∏ j, B (d.2 j)) *
    (∏ j : Fin (L-t), F (d.1 (row L t ht (.inl j))) (some (d.2 (col L t ht (.inr j))))) *
    ∏ j : Fin t, F (d.1 (row L t ht (.inr j))) none

omit [Fintype Y] [Fintype X] in
private theorem blocks_value (A : Y → R) (B : X → R) (F : Y → Option X → R)
    (L t : ℕ) (ht : t ≤ L) (d : Blocks Y X L t) :
    value A B F L t ht (assignments Y X L t ht d) =
      (∏ j, A (d.1 j).1 * B (d.1 j).2 * F (d.1 j).1 (some (d.1 j).2)) *
      (∏ j, A (d.2.1 j) * F (d.2.1 j) none) *
      ∏ j, B (d.2.2 j) := by
  let z := assignments Y X L t ht d
  have hm (j : Fin (L-t)) : z.1 (row L t ht (.inl j))=(d.1 j).1 :=
    rows_interior Y X L t ht d j
  have hc (j : Fin (L-t)) : z.2 (col L t ht (.inr j))=(d.1 j).2 :=
    cols_interior Y X L t ht d j
  have hYm (j : Fin t) : z.1 (row L t ht (.inr j))=d.2.1 j := by
    change Sum.elim (fun v => (d.1 v).1) d.2.1 ((row L t ht).symm (row L t ht (.inr j))) = _
    simp
  have hXm (j : Fin t) : z.2 (col L t ht (.inl j))=d.2.2 j := by
    change Sum.elim d.2.2 (fun v => (d.1 v).2) ((col L t ht).symm (col L t ht (.inl j))) = _
    simp
  have hR : (∏ j, A (z.1 j)) = (∏ i, A (d.1 i).1)*(∏ j, A (d.2.1 j)) := by
    rw [← Equiv.prod_comp (row L t ht) (fun j => A (z.1 j)),Fintype.prod_sum_type]
    simp only [hm,hYm]
  have hC : (∏ j, B (z.2 j)) = (∏ j, B (d.2.2 j))*(∏ i, B (d.1 i).2) := by
    rw [← Equiv.prod_comp (col L t ht) (fun j => B (z.2 j)),Fintype.prod_sum_type]
    simp only [hc,hXm]
  change value A B F L t ht z = _
  simp only [value,hR,hC,hm,hc,hYm,Finset.prod_mul_distrib]
  ring

/-- Retaining every original Boolean row/column assignment gives these
three exact powers; the exponents are cardinalities, not supplied factors. -/
theorem layer_partition (A : Y → R) (B : X → R) (F : Y → Option X → R)
    (L t : ℕ) (ht : t ≤ L) :
    (∑ d : (Fin L → Y) × (Fin L → X), value A B F L t ht d) =
      (∑ p : Y×X, A p.1 * B p.2 * F p.1 (some p.2))^(L-t) *
        (∑ y : Y, A y * F y none)^t *
        (∑ x : X, B x)^t := by
  classical
  rw [← Equiv.sum_comp (assignments Y X L t ht) (value A B F L t ht)]
  simp only [blocks_value]
  let M := fun (u : Fin (L-t)→Y×X) => ∏ j, A (u j).1*B (u j).2*F (u j).1 (some (u j).2)
  let A₀ := fun (u : Fin t→Y) => ∏ j, A (u j) * F (u j) none
  let B₀ := fun (u : Fin t→X) => ∏ j, B (u j)
  change (∑ d : Blocks Y X L t, M d.1 * A₀ d.2.1 * B₀ d.2.2) = _
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type,← Finset.mul_sum,← Finset.sum_mul]
  have hM : (∑ u, M u) = (∑ p : Y×X, A p.1*B p.2*F p.1 (some p.2))^(L-t) := by
    unfold M
    rw [← Fintype.prod_sum (fun (_ : Fin (L-t)) (p : Y×X) => A p.1*B p.2*F p.1 (some p.2))]
    simp
  have hA : (∑ u, A₀ u) = (∑ y : Y, A y*F y none)^t := by
    unfold A₀
    rw [← Fintype.prod_sum (fun (_ : Fin t) (y : Y) => A y*F y none)]
    simp
  have hB : (∑ u, B₀ u) = (∑ x : X, B x)^t := by
    unfold B₀
    rw [← Fintype.prod_sum]
    simp
  rw [hM,hA,hB,Fintype.sum_prod_type]

#print axioms layer_partition
end J6OrientedLayerProduct
