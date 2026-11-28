import P5H4SharpComplete
import P5LiteralJets

/-! The two short source-visible examples following the jet-minor
counterexamples in §2.3. These use the actual evaluation and quotient maps. -/
namespace Paper5.HermiteExamples
open Polynomial Matrix
open scoped Polynomial Classical

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 6000000

noncomputable section

def zeroColumnMatrix (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) K[X] :=
  Matrix.diagonal (fun i => if i=0 then 1 else 0)

theorem zero_column_means_deficiency_at_every_node_and_zero_det
    (K : Type*) [Field K] :
    (∀ i,zeroColumnMatrix K i 1=0) ∧ (zeroColumnMatrix K).det=0 ∧
      ∀ t : K, ((zeroColumnMatrix K).map (evalRingHom t)).rank=1 := by
  classical
  refine ⟨?_,?_,?_⟩
  · intro i
    by_cases h : i=(1:Fin 2)
    · subst i
      simp [zeroColumnMatrix]
    · simp [zeroColumnMatrix,Matrix.diagonal_apply_ne _ h]
  · rw [zeroColumnMatrix,Matrix.det_diagonal,Fin.prod_univ_two]
    simp
  · intro t
    have h : (zeroColumnMatrix K).map (evalRingHom t) =
        Matrix.diagonal (fun i : Fin 2 => if i=0 then (1:K) else 0) := by
      rw [zeroColumnMatrix,Matrix.diagonal_map (map_zero (evalRingHom t))]
      congr 1
      funext i
      by_cases hi : i=(0:Fin 2) <;> simp [hi]
    rw [h,Matrix.rank_diagonal]
    let e : {i : Fin 2 // (if i=0 then (1:K) else 0)≠0} ≃ Unit :=
      { toFun := fun _=>()
        invFun := fun _=>⟨0,by simp⟩
        left_inv := fun i=>by
          apply Subtype.ext
          have hi : i.val=(0:Fin 2) := by
            by_contra hn
            exact i.property (by simp [hn])
          exact hi.symm
        right_inv := fun a=>by cases a; rfl }
    calc
      Fintype.card _ = Fintype.card Unit := Fintype.card_congr e
      _ = 1 := by simp

theorem nonzero_constant_diagonal_hides_in_residue
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n] [Nonempty n]
    (π : R) (hπ : π≠0) [Nontrivial (R ⧸ Ideal.span ({π}:Set R))] :
    let A : Matrix n n R := Matrix.diagonal (fun _=>π)
    let f := Ideal.Quotient.mk (Ideal.span ({π}:Set R))
    A≠0 ∧ A.map f=0 ∧ (A.map f).rank=0 := by
  dsimp only
  let I : Ideal R := Ideal.span ({π}:Set R)
  have hq : Ideal.Quotient.mk I π=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hmap : (Matrix.diagonal (fun _ : n=>π)).map (Ideal.Quotient.mk I)=0 := by
    rw [Matrix.diagonal_map (map_zero (Ideal.Quotient.mk I))]
    simp only [hq,Matrix.diagonal_zero]
  exact ⟨fun h=>hπ (by
    let i : n := Classical.choice ‹Nonempty n›
    simpa only [Matrix.diagonal_apply_eq,Matrix.zero_apply] using
      congrArg (fun M : Matrix n n R=>M i i) h), hmap,
    hmap ▸ Matrix.rank_zero⟩

#print axioms zero_column_means_deficiency_at_every_node_and_zero_det
#print axioms nonzero_constant_diagonal_hides_in_residue
end
end Paper5.HermiteExamples
