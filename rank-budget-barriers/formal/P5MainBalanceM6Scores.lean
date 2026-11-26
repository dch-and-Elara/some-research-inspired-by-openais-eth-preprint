import P5MainBalanceM6Input
import P5MainBalanceM6Recipe
import P5MainBalanceLayout

/-! The actual fibre evaluator: representatives are chosen only from
the measured Boolean fibre, and each factor evaluator receives only
the signs owned by its actual factor group. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Polynomial
open scoped BigOperators Classical

variable {E W F Copy I B V : Type*} [Fintype E] [Fintype W] [Fintype F] [Fintype Copy]
  [Fintype I] [Fintype B] [LinearOrder B]

def signedOwner (L : SourceLayout E W F Copy I B) (mark : V↪E) : V→F :=
  L.factor ∘ mark

abbrev SourceRecipe (L : SourceLayout E W F Copy I B) (mark : V↪E) :=
  Recipe L.factor (signedOwner L mark) ℚ[X]

noncomputable def actualH (L : SourceLayout E W F Copy I B) (mark : V↪E) (t : I→ℚ)
    (M : Mix Copy I B) (P : SourceRecipe L mark) (σ : V→Bool) : Bivariate :=
  ∑ x : W→Bool,P.evaluate σ (originalInput L t M x)

noncomputable def actualPatch (L : SourceLayout E W F Copy I B) (mark : V↪E) (t : I→ℚ)
    (M : Mix Copy I B) (P : SourceRecipe L mark) (i : I) (σ : V→Bool)
    (x : W→Bool) (U : Finset W) : Bivariate :=
  P.evaluate σ (nativeInput L t M i x U)

theorem centered_actualH (L : SourceLayout E W F Copy I B) (mark : V↪E) (t : I→ℚ)
    (M : Mix Copy I B) (P : SourceRecipe L mark) (i : I) (σ : V→Bool) :
    centerBivar (t i) (actualH L mark t M P σ) =
      ∑ x : W→Bool,actualPatch L mark t M P i σ x (Finset.univ.filter fun w=>x w) := by
  rw [←shiftNative_eq]
  unfold actualH actualPatch Recipe.evaluate Recipe.factorScore
  simp only [map_sum,map_prod,map_mul,shiftNative_C,nativeInput_trueBits]

theorem actualPatch_small_window [Nonempty W]
    (L : SourceLayout E W F Copy I B) (mark : V↪E) (t : I→ℚ)
    (M : Mix Copy I B) (P : SourceRecipe L mark) (i : I) (σ : V→Bool)
    (x : W→Bool) (j : ℕ) :
    (actualPatch L mark t M P i σ x (Finset.univ.filter fun w=>x w)).coeff j =
      window (Finset.univ.filter fun w=>x w) j
        (fun U=>(actualPatch L mark t M P i σ x U).coeff j) := by
  unfold actualPatch nativeInput
  exact P.low_window σ _ _ _ j

abbrev ActualY (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B) (i : I) :=
  Set.range (sourceTuple keep L i)

noncomputable instance actualYFinite (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (i : I) : Fintype (ActualY keep L i) :=
  (Set.finite_range _).fintype

noncomputable def fibreRep (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B) (i : I)
    (y : ActualY keep L i) : W→Bool :=
  Classical.choose y.property

omit [Fintype F] in
theorem fibreRep_exact (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B) (i : I)
    (y : ActualY keep L i) :
    sourceTuple keep L i (fibreRep keep L i y)=y.val :=
  Classical.choose_spec y.property

noncomputable def localCandidate (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B) (i : I)
    (y : ActualY keep L i) (g : B) (x : GroupBits (fun w=>L.a w i) g) : W→Bool :=
  fun w=>if h : L.a w i=g then x ⟨w,h⟩ else fibreRep keep L i y w

omit [Fintype F] in
theorem localCandidate_agrees (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B) (i : I)
    (y : ActualY keep L i) (g : B) (x : W→Bool) (w : W) (hw : L.a w i=g) :
    localCandidate keep L i y g (restrictGroup (fun w=>L.a w i) x g) w=x w := by
  simp [localCandidate,restrictGroup,hw]

omit [Fintype F] in
private theorem group_measure_congr (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B) (i : I) (g : B)
    (x z : W→Bool) (h : ∀ w,L.a w i=g → x w=z w) :
    sourceTuple keep L i x g=sourceTuple keep L i z g := by
  unfold sourceTuple
  apply congrArg (Matrix.mulVec (exceptionalMatrix keep L))
  funext w
  by_cases hw : L.a w i=g
  · simp [hw,h w hw]
  · simp [hw]

omit [Fintype F] in
theorem localCandidate_measure (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B) (i : I)
    (y : ActualY keep L i) (g : B) (x : W→Bool) (hy : sourceTuple keep L i x=y.val) :
    sourceTuple keep L i (localCandidate keep L i y g (restrictGroup (fun w=>L.a w i) x g)) =
      sourceTuple keep L i x := by
  funext h
  by_cases hh : h=g
  · subst h
    exact group_measure_congr keep L i g _ _
      (fun w hw=>localCandidate_agrees keep L i y g x w hw)
  · calc
      _ = sourceTuple keep L i (fibreRep keep L i y) h :=
        group_measure_congr keep L i h _ _ fun w hw=>by
          have hn : L.a w i≠g := hw ▸ hh
          simp [localCandidate,hn]
      _ = _ := by rw [fibreRep_exact,hy]

noncomputable def actualGroupScore (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (mark : V↪E) (t : I→ℚ) (M : Mix Copy I B) (P : SourceRecipe L mark)
    (i : I) (U : Finset W) (y : ActualY keep L i)
    (g : B) (σ : {v : V//pinWord L mark v i=g}→Bool)
    (x : GroupBits (fun w=>L.a w i) g) : Bivariate :=
  P.groupScore (fun f=>L.d f i) g σ
    (nativeInput L t M i (localCandidate keep L i y g x) U)

noncomputable def actualMacro (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (mark : V↪E) (t : I→ℚ) (M : Mix Copy I B) (P : SourceRecipe L mark)
    (i : I) (S U : Finset W) (y : ActualY keep L i) :
    GroupProducts.GroupTerm (pinWord L mark) Bivariate :=
  actualFibreMacro (pinWord L mark) i (fun w=>L.a w i)
    (actualGate keep L i S y.val) (actualGroupScore keep L mark t M P i U y)

set_option maxHeartbeats 9800000 in
theorem actualMacro_value (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (mark : V↪E) (t : I→ℚ) (M : Mix Copy I B) (hM : ActualBaseInvariant keep L M)
    (P : SourceRecipe L mark) (i : I) (hi : t i≠0) (S U : Finset W)
    (y : ActualY keep L i) (σ : V→Bool) :
    (actualMacro keep L mark t M P i S U y).value σ =
      ∑ x : {x : W→Bool // sourceTuple keep L i x=y.val ∧ ∀ w∈S,x w=true},
        actualPatch L mark t M P i σ x.val U := by
  unfold actualMacro
  rw [source_fibre_update_is_group_term]
  apply Finset.sum_congr rfl
  intro x _
  change (∏ g,actualGroupScore keep L mark t M P i U y g (fun v=>σ v.val)
     (restrictGroup (fun w=>L.a w i) x.val g))=_
  unfold actualPatch
  rw [←P.regroup (fun f=>L.d f i) σ (nativeInput L t M i x.val U)]
  apply Finset.prod_congr rfl
  intro g _
  unfold actualGroupScore
  apply P.groupScore_congr
  intro e he
  apply nativeInput_actual_local keep L t M hM i hi e U
  · exact localCandidate_measure keep L i y g x.val x.property.1
  · intro w hw
    exact localCandidate_agrees keep L i y g x.val w (hw.trans he)

#print axioms centered_actualH
#print axioms actualPatch_small_window
#print axioms fibreRep_exact
#print axioms localCandidate_agrees
#print axioms localCandidate_measure
#print axioms actualMacro_value
end P5MainBalance.M6
