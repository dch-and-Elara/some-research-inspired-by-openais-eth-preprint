import P5AlwaysSatOriginalTaylorChart
import P5AlwaysSatOriginalTaylorWords
import P5MainBalanceM6Grade
import P5MainBalanceM6SparseCompiler

/-! The literal switched clauses become actual typed MAIN rational
factors (including the width-three guard), not a black-box coefficient
oracle. The same recipe is proved at arbitrary inputs and at zero. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainBalance P5MainIterator P5MainBalance.M6 P5MainBalance.M6.Sparse Polynomial
open scoped BigOperators Classical Polynomial

variable {V Copy I B : Type*} [Fintype V] [LinearOrder B]
variable {E : Finset (V×V)} {T : Finset V}
variable (L : SourceLayout (ClausePort E T) (Port E T) (CloneFactor E T) Copy I B)
variable (ho : L.placement.owner=portOwner E T) (hf : L.factor=portFactor E T)

local notation "D" => directChart L ho hf

noncomputable def directWords (f : CloneFactor E T) :
    Fin (Fintype.card (Choices ((D).literals f))+1)→List (FactorFibre E T f) :=
  Fin.cases [] (fun k=>subword ((D).literals f) (choiceCode ((D).literals f) k))

noncomputable def directWeights (f : CloneFactor E T) (s : (D).Signs f) :
    Fin (Fintype.card (Choices ((D).literals f))+1)→ℚ :=
  Fin.cases 1 (fun k=>-wordWeight ((D).literals f) ((D).localSign f s)
    signedLetter (choiceCode ((D).literals f) k))

noncomputable def directRecipe : SourceRecipe L (D).mark where
  count f := Fintype.card (Choices ((D).literals f))+1
  degree f k := (directWords L ho hf f k).length
  read f k j := (D).scoped f ((directWords L ho hf f k).get j)
  coeff f k s := Polynomial.C (directWeights L ho hf f s k)

noncomputable def directBase (f : CloneFactor E T) : ℕ := ((D).literals f).length

theorem direct_grade :
    (directRecipe L ho hf).graded (directBase L ho hf) 0 := by
  intro f k s j hj
  change (directWords L ho hf f k).length≤((D).literals f).length+0*j
  unfold directWords
  refine Fin.cases ?_ (fun v=>?_) k
  · simp
  · exact (subword_length ((D).literals f) (choiceCode ((D).literals f) v)).trans (by simp)

theorem direct_nominal :
    (∑ f,directBase L ho hf f)=Fintype.card (ClausePort E T) := by
  have h (f : CloneFactor E T) : directBase L ho hf f=Nat.card (FactorFibre E T f) :=
    ((D).literal_count (fun _=>false) f).trans (factor_fibre_card E T (fun _=>false) f).symm
  simp_rw [h]
  rw [←Nat.card_sigma,Nat.card_congr (Equiv.sigmaFiberEquiv (portFactor E T)),
    Nat.card_eq_fintype_card]

set_option maxHeartbeats 1800000 in
theorem direct_expansion {R : Type*} [CommRing R] (ι : ℚ→+*R)
    (f : CloneFactor E T) (s : (D).Signs f) (Y : FactorFibre E T f→R) :
    (∑ k,ι (directWeights L ho hf f s k)*letters (directWords L ho hf f k) Y) =
      1-letters ((D).literals f) (fun e=>if (D).localSign f s e then 1-Y e else Y e) := by
  rw [Fin.sum_univ_succ]
  have hEmpty : letters ([] : List (FactorFibre E T f)) Y=(1:R) := rfl
  simp only [directWeights,directWords,Fin.cases_zero,Fin.cases_succ,map_one,
    map_neg,hEmpty,mul_one,neg_mul]
  have he := (choiceCode ((D).literals f)).sum_comp (fun pick=>
    ι (wordWeight ((D).literals f) ((D).localSign f s) signedLetter pick)*
      letters (subword ((D).literals f) pick) Y)
  rw [Finset.sum_neg_distrib,he]
  simp only [signed_word_map]
  rw [signed_word_expansion,sub_eq_add_neg]

theorem direct_factor_literal (A : ClausePort E T→Bivariate)
    (f : CloneFactor E T) (s : (D).Signs f) :
    (directRecipe L ho hf).factorScore f s A =
      1-letters ((D).literals f) (fun p=>if (D).localSign f s p then 1-A p.val else A p.val) := by
  let ι : ℚ→+*Bivariate := Polynomial.C.comp Polynomial.C
  unfold Recipe.factorScore
  change (∑ k,ι (directWeights L ho hf f s k) *
      ∏ j : Fin (directWords L ho hf f k).length,A ((directWords L ho hf f k).get j).val)=_
  let Y : FactorFibre E T f→Bivariate := fun p=>A p.val
  calc
    _ = ∑ k,ι (directWeights L ho hf f s k)*letters (directWords L ho hf f k) Y := by
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun z=>ι (directWeights L ho hf f s k)*z)
        (product_get_eq_letters (directWords L ho hf f k) Y)
    _ = _ := direct_expansion L ho hf ι f s Y

theorem direct_anchor_literal (f : CloneFactor E T) (s : (D).Signs f) (x : Port E T→Bool) :
    atAnchorFactor L (D).mark (directRecipe L ho hf) f s x =
      if (D).localEval f s x=true then 1 else 0 := by
  unfold atAnchorFactor
  change (∑ k,Polynomial.C (directWeights L ho hf f s k)*
    ∏ j : Fin (directWords L ho hf f k).length,
      Polynomial.C (qbits x (L.placement.owner ((directWords L ho hf f k).get j).val)))=_
  let Y : FactorFibre E T f→ℚ[X] := fun p=>Polynomial.C (qbits x (L.placement.owner p.val))
  have he : (∑ k,Polynomial.C (directWeights L ho hf f s k)*
      ∏ j : Fin (directWords L ho hf f k).length,Y ((directWords L ho hf f k).get j)) =
        ∑ k,Polynomial.C (directWeights L ho hf f s k)*letters (directWords L ho hf f k) Y := by
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun z=>Polynomial.C (directWeights L ho hf f s k)*z)
      (product_get_eq_letters (directWords L ho hf f k) Y)
  change (∑ k,Polynomial.C (directWeights L ho hf f s k)*
    ∏ j : Fin (directWords L ho hf f k).length,Y ((directWords L ho hf f k).get j))=_
  rw [he,direct_expansion L ho hf (Polynomial.C : ℚ→+*ℚ[X]) f s]
  dsimp only [Y]
  have hb (p : FactorFibre E T f) :
      Polynomial.C (qbits x (L.placement.owner p.val))=
        bitValueAux (K:=ℚ[X]) (x (L.placement.owner p.val)) := by
    cases h : x (L.placement.owner p.val) <;>
      simp [qbits,BooleanMeasurement.bit,h,bitValueAux]
  simp_rw [hb]
  rw [letters_false_truth]
  change 1-(if (D).localEval f s x=true then (0:ℚ[X]) else 1)=_
  split <;> simp

variable [Fintype Copy] [Fintype I] [Fintype B]

theorem direct_terminal_exact (t : I→ℚ) (M : Mix Copy I B) (σ : V→Bool) :
    retainedOrigin 1 (actualH L (D).mark t M (directRecipe L ho hf) σ) =
      (PinnedCNF.modelCount (cloneCNF E T σ):ℚ) := by
  rw [direct_anchor_count_from_literal_factors L (D).mark t M (directRecipe L ho hf)
    (fun f s x=>(D).localEval f s x=true)
    (fun f s x=>by
      rw [direct_anchor_literal L ho hf]
      by_cases hx : (D).localEval f s x=true <;> simp [hx])]
  congr 1
  unfold nativeModelCount PinnedCNF.modelCount
  rw [Fintype.card_subtype]
  congr 1
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hh : (∀ f,(D).localEval f (fun v=>σ v.val) x=true) ↔
      ∀ f,(clonedClause E T σ f).eval x=true := by
    apply forall_congr'
    intro f
    rw [(D).local_eval_global f σ x]
  exact hh.trans ((all_cloned_clauses E T σ x).symm.trans (Std.Sat.CNF.sat_def _ _))

theorem direct_terminal_witness (t : I→ℚ) (M : Mix Copy I B) :
    ∃ out : (V→Bool)→ℤ,
      (∀ σ,(out σ:ℚ)=retainedOrigin 1 (actualH L (D).mark t M (directRecipe L ho hf) σ)) ∧
      (∀ σ,(out σ:ZMod 2)=(PinnedCNF.modelCount (PinnedCNF.formula E σ):ZMod 2)) := by
  refine ⟨fun σ=>(PinnedCNF.modelCount (cloneCNF E T σ):ℤ),?_,?_⟩
  · intro σ
    rw [direct_terminal_exact L ho hf t M,Int.cast_natCast]
  · intro σ
    rw [Int.cast_natCast,←ZMod.natCast_mod (PinnedCNF.modelCount (cloneCNF E T σ)) 2,
      cloned_count_parity]

#print axioms direct_grade
#print axioms direct_nominal
#print axioms direct_expansion
#print axioms direct_factor_literal
#print axioms direct_anchor_literal
#print axioms direct_terminal_exact
#print axioms direct_terminal_witness
end Paper5.AlwaysSatOriginal.Physical.Taylor