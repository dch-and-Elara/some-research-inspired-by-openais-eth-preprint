import AffineEdgeEncoder
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases

open scoped Polynomial
open AffineEdge

namespace Reconstruction.ReleaseColor

noncomputable section

/-- The second endpoint of Theorem 1 as an attained minimum over arbitrary
finite matrices. Choosing ternary rows imposes no extra cost over the rationals,
because the attaining rows have only zero and one as entries. -/
theorem boundary_exact_minimum {F : Type*} [Field F] {q : ℕ}
    (sites : Fin q → F) (hq : 2 ≤ q) (hi : Function.Injective sites)
    (hn : ∀ t, sites t ≠ 0) (ternary : Bool) :
    IsLeast {k : ℕ | ∃ (m : ℕ) (C : Matrix (Fin m) (Word q) F)
      (P : Word q → Word q → F[X]),
      PairedCondition sites C (q-2) P ∧
        (ternary = true → ∀ i v, C i v = -1 ∨ C i v = 0 ∨ C i v = 1) ∧ C.rank = k}
      (q+(q+1)/2+2) := by
  classical
  obtain ⟨⟨P,hp⟩, hr⟩ := binaryEncoder_attains sites hq hi hn
  let e := Fintype.equivFin (EncoderRow q)
  let D := (binaryEncoder (F := F) q).reindex e (Equiv.refl _)
  have hD : PairedCondition sites D (q-2) P := by
    refine ⟨hp.1,hp.2.1, fun u t z hmeas hside => hp.2.2 u t z ?_ hside⟩
    intro i
    simpa [D] using hmeas (e i)
  have hbinary (j : Fin (Fintype.card (EncoderRow q))) (v : Word q) :
      D j v = 0 ∨ D j v = 1 :=
    binaryEncoder_binary (e.symm j) v
  refine ⟨⟨_, D, P, hD, fun _ j v => Or.inr (hbinary j v), ?_⟩, ?_⟩
  · exact (Matrix.rank_reindex e (Equiv.refl _) (binaryEncoder (F := F) q)).trans hr
  · rintro k ⟨m,C,Q,hQ,-,rfl⟩
    exact paired_rank_lower hq hi hn hQ

/-- At least two distinct nonzero sites cannot be taken from the prime field with
two elements. Fields of characteristic two with enough sites are covered above. -/
theorem no_two_nonzero_sites_in_F2 {q : ℕ} (hq : 2 ≤ q) (a : Fin q → ZMod 2)
    (hi : Function.Injective a) (hn : ∀ t, a t ≠ 0) : False := by
  have hcases (x : ZMod 2) : x = 0 ∨ x = 1 := by fin_cases x <;> first | exact Or.inl rfl | exact Or.inr rfl
  have h (t : Fin q) : a t = 1 := (hcases _).resolve_left (hn t)
  let s : Fin q := ⟨0, by omega⟩
  let t : Fin q := ⟨1, by omega⟩
  have he := congrArg Fin.val (hi ((h s).trans (h t).symm))
  exact Nat.zero_ne_one he

end
end Reconstruction.ReleaseColor
