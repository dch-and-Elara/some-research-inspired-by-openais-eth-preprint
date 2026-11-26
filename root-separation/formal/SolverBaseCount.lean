import SolverRoot

noncomputable section
namespace RootSeparation.Solver
open Polynomial Entry S11

theorem wordConstant_zero_coord {f : ℤ[X]} {e p : ℕ} (hf : f.Monic) (he : f.natDegree = e)
    (hp : 0 < p) (hepos : 0 < e) (m : ℕ) :
    wordCoords hf he p hp (m : WordRing f p) ⟨0,hepos⟩ = (m : ZMod (2^p)) := by
  haveI : Fact (1 < 2^p) := ⟨Nat.one_lt_two_pow hp.ne'⟩
  let g := f.map (integerToWord p)
  have hg : g.Monic := hf.map _
  have hd : g.natDegree = e := (hf.natDegree_map _).trans he
  have hm : (m : WordRing f p) = AdjoinRoot.mk g (C (m : ZMod (2^p))) := by
    exact (map_natCast (AdjoinRoot.of g) m).symm
  rw [hm,wordCoords,coordinate_mk]
  have hlt : (C (m : ZMod (2^p))).degree < g.degree := by
    apply degree_C_le.trans_lt
    rw [degree_eq_natDegree hg.ne_zero, hd]
    exact WithBot.coe_lt_coe.2 hepos
  rw [modByMonic_eq_self_iff hg |>.2 hlt, coeff_C_zero]

section Entry
open GraphCutMoments
variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (σ : V → Bool)
variable (F : SourcePolynomial (4*lambda (size E)))

def rootConstant (ep : 0 < 4*lambda (size E))
    (x : WordRing F.f (initialPrecision (V := V))) : ℕ :=
  (wordCoords F.monic F.degree (initialPrecision (V := V)) (Nat.succ_pos _) x ⟨0,ep⟩).val

omit [DecidableEq V] in
theorem rootConstant_count (ep : 0 < 4*lambda (size E)) :
    rootConstant E F ep (PinnedCNF.modelCount (PinnedCNF.formula E σ)) =
      PinnedCNF.modelCount (PinnedCNF.formula E σ) := by
  unfold rootConstant
  rw [wordConstant_zero_coord]
  apply ZMod.val_natCast_of_lt
  have h : PinnedCNF.modelCount (PinnedCNF.formula E σ) ≤ 1 := by
    rw [PinnedCNF.count_eq_indicator]
    split <;> decide
  exact h.trans_lt (Nat.one_lt_two_pow (Nat.succ_ne_zero _))

theorem rootLeaf_count (ep : 0 < 4*lambda (size E)) :
    rootConstant E F ep (leafValue (rootCall E reg σ F)) =
      PinnedCNF.modelCount (PinnedCNF.formula E σ) := by
  rw [rootLeaf_word, rootConstant_count]

end Entry

#print axioms wordConstant_zero_coord
#print axioms rootConstant_count
#print axioms rootLeaf_count

end RootSeparation.Solver
