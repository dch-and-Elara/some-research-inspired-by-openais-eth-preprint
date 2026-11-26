import RBSharp
import Mathlib.Data.Finset.Sort

/-! Order statistics used to rewrite the determinantal gcd minimum as the
sum of the s smallest local exponents. Ties keep all coordinates. -/
namespace P5H4
open scoped BigOperators Classical

/-- Any finite injective address list can be sorted by a permutation of
its original addresses, rather than deleting repetitions of weights. -/
theorem reorder_embedding {α : Type*} [LinearOrder α] {s : ℕ}
    (g : Fin s → α) (hg : Function.Injective g) :
    ∃ σ : Equiv.Perm (Fin s), StrictMono (fun i => g (σ i)) := by
  let S := Finset.univ.image g
  have hcard : S.card = s := by
    simp [S,Finset.card_image_of_injective Finset.univ hg]
  let E : Fin s → S := fun x => ⟨g x,Finset.mem_image.mpr ⟨x,Finset.mem_univ x,rfl⟩⟩
  have hin : Function.Injective E := fun i j h => hg (congrArg Subtype.val h)
  have hs : Function.Surjective E := by
    intro y
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp y.property
    exact ⟨x,Subtype.ext hx⟩
  let B : Fin s ≃ S := Equiv.ofBijective E ⟨hin,hs⟩
  let D := S.orderIsoOfFin hcard
  let σ : Equiv.Perm (Fin s) := D.toEquiv.trans B.symm
  have he (i : Fin s) : g (σ i) = (D i : α) :=
    congrArg Subtype.val (B.apply_symm_apply (D i))
  refine ⟨σ,fun i j hij => ?_⟩
  change g (σ i) < g (σ j)
  rw [he,he]
  exact D.strictMono hij

theorem sort_weights {r : ℕ} (w : Fin r → ℕ) :
    ∃ σ : Equiv.Perm (Fin r), Monotone (fun i => w (σ i)) := by
  let g (i : Fin r) : ℕ ×ₗ Fin r := toLex (w i,i)
  have hg : Function.Injective g := fun i j h =>
    congrArg (fun x : ℕ ×ₗ Fin r => (ofLex x).2) h
  obtain ⟨σ,hσ⟩ := reorder_embedding g hg
  exact ⟨σ,Prod.Lex.monotone_fst_ofLex.comp hσ.monotone⟩

theorem index_le_of_strictMono {s r : ℕ} (u : Fin s → Fin r) (hu : StrictMono u) (i : Fin s) :
    i.val ≤ (u i).val := by
  cases s with
  | zero => exact Fin.elim0 i
  | succ s =>
    induction i using Fin.induction with
    | zero => exact Nat.zero_le _
    | succ i ih =>
      have hi : i.castSucc < i.succ := Fin.castSucc_lt_succ i
      have hj : (u i.castSucc).val < (u i.succ).val := hu hi
      change i.val ≤ (u i.castSucc).val at ih
      change i.val+1 ≤ (u i.succ).val
      omega

/-- Monotonicity plus injectivity gives the exact least prefix weight. -/
theorem prefix_minimum {s r : ℕ} (hs : s ≤ r) (w : Fin r → ℕ) (hw : Monotone w)
    (u : Fin s → Fin r) (hu : Function.Injective u) :
    (∑ i, w (Fin.castLE hs i)) ≤ ∑ i, w (u i) := by
  obtain ⟨σ,hσ⟩ := reorder_embedding u hu
  calc
    _ ≤ ∑ i, w (u (σ i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact hw (index_le_of_strictMono _ hσ i)
    _ = _ := Fintype.sum_equiv σ _ _ (fun _ => rfl)

theorem sorted_prefix_minimum {s r : ℕ} (hs : s ≤ r) (w : Fin r → ℕ)
    (σ : Equiv.Perm (Fin r)) (hσ : Monotone (fun i => w (σ i))) :
    let v := ∑ i, w (σ (Fin.castLE hs i))
    (∀ u : Fin s → Fin r, Function.Injective u → v ≤ ∑ i, w (u i)) ∧
      ∃ u : Fin s → Fin r, Function.Injective u ∧ v = ∑ i, w (u i) := by
  constructor
  · intro u hu
    have h := prefix_minimum hs (fun i => w (σ i)) hσ (σ.symm ∘ u) (σ.symm.injective.comp hu)
    simpa [Function.comp_def] using h
  · exact ⟨σ ∘ Fin.castLE hs,σ.injective.comp (Fin.castLE_injective hs),rfl⟩

#print axioms reorder_embedding
#print axioms sort_weights
#print axioms prefix_minimum
#print axioms sorted_prefix_minimum
end P5H4
