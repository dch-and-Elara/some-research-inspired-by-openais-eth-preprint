import J6R14SpecializedBoxPackedFile
import J9R13PhysicalTables
import J6R11IntegralRetained

/-! Check the two original tensor sides against the literal R13
compiler. The column system is the actual conjunction of its pin
and ordinary-clause table factors, not a callback given by an
unrelated aggregate contraction. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial J6R9Recursive J6R10Repack J6R11Integral
open J8Physical J8EndToEnd J8J9Grouped LiteralPortCompiler

noncomputable section
variable {Packet R S V G : Type} {P : V→Type} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

set_option linter.unusedSectionVars false in
theorem oriented_rows_exact (f : ℤ[X]) (ell p : ℕ) (F : OldTables d) (sign : S→Bool)
    (hf : f.Monic) (hp : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell) (Y : Wire R→Bool) :
    rowProduct (orientedNetwork d) (orientedEntryFile d f ell p F sign) hf Y =
      (truth J9LayoutTransfer.allRows Y : IntRing f ell) := by
  unfold rowProduct J9LayoutTransfer.allRows
  rw [J9LayoutTransfer.listedRows_truth,Finset.prod_map_toList]
  refine Finset.prod_congr rfl ?_
  intro r _
  rw [oriented_row_truth d f ell p F sign hf hp hF hℓ Y r,truth_equality]
  rfl

set_option linter.unusedSectionVars false in
theorem oriented_cols_exact (f : ℤ[X]) (ell p : ℕ) (F : OldTables d) (sign : S→Bool)
    (hf : f.Monic) (hp : 0<p) (hF : 0<f.natDegree) (hℓ : 0<ell) (X : Wire R→Bool)
    {M : ℕ} (idx : Wire R≃Fin M) :
    colProduct (orientedNetwork d) (orientedEntryFile d f ell p F sign) hf X =
      (truth (J9R13PhysicalTables.globalCNF d idx F sign) (X ∘ idx.symm) : IntRing f ell) := by
  let A := IntRing f ell
  let C := orientedEntryFile d f ell p F sign
  let S₀ (s : S) : A := (C (.inr (.inl s))).frozen hf
    (assignment (orientedNetwork d) X (.inr (.inl s)))
  let V₀ (v : V) : A := (C (.inr (.inr v))).frozen hf
    (assignment (orientedNetwork d) X (.inr (.inr v)))
  let U : Cube d := fun g => localLabels d g X
  have H := J9R13PhysicalTables.global_truth d (K:=A) idx F sign U
  have hIdx : cubeEquiv d idx U = X ∘ idx.symm := by
    funext j
    exact localLabels_cube d X (idx.symm j)
  rw [hIdx,Finset.prod_mul_distrib] at H
  rw [H]
  unfold colProduct
  rw [Fintype.prod_sum_type]
  change (∏ s : S,S₀ s) * (∏ v : V,V₀ v) = _
  have hPins : (∏ s : S,S₀ s) =
      ∏ g : G, ∏ s : LocalPin d g, (truth (pin s (sign s.val)) (U g).1 : A) := by
    calc
      _ = ∏ s : (Σ g,LocalPin d g), S₀ s.2.val := by
        exact (Fintype.prod_equiv (Equiv.sigmaFiberEquiv d.pinLabel) _ _ (fun _ => rfl)).symm
      _ = _ := by
        rw [Fintype.prod_sigma]
        refine Finset.prod_congr rfl ?_
        intro g _
        refine Finset.prod_congr rfl ?_
        intro s _
        exact oriented_pin_truth d f ell p F sign hf hp hF hℓ X g s
  have hOld : (∏ v : V,V₀ v) =
      ∏ g : G, ∏ v : LocalColumn d g, (truth (F g v) ((U g).2 v) : A) := by
    calc
      _ = ∏ v : (Σ g,LocalColumn d g), V₀ v.2.val := by
        exact (Fintype.prod_equiv (Equiv.sigmaFiberEquiv d.colLabel) _ _ (fun _ => rfl)).symm
      _ = _ := by
        rw [Fintype.prod_sigma]
        refine Finset.prod_congr rfl ?_
        intro g _
        refine Finset.prod_congr rfl ?_
        intro v _
        exact oriented_old_truth d f ell p F sign hf hp hF hℓ X g v
  rw [hPins,hOld]
  apply congrArg₂ (·*·)
  all_goals
    refine Finset.prod_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) ?_
    intro g _
    refine Finset.prod_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) ?_
    intro u _
    rfl

#print axioms oriented_rows_exact
#print axioms oriented_cols_exact
end
end J6R14SpecializedBox
