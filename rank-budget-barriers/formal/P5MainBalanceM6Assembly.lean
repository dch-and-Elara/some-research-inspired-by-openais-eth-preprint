import P5MainBalanceM6Scores
import P5MainBalanceM6Grouping
import P5MainBalanceM6JetImage
import P5MainBalanceM6Trim

/-! Exact M.6 low-order readout of the literal source monomial lists,
placed rows and real linear-statistic fibres. This is a representation
identity, not an assumption that any implementation enumerates it. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Polynomial
open scoped BigOperators Classical

variable {E W F Copy I B V : Type*} [Fintype E] [Fintype W] [Nonempty W]
  [Fintype F] [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

noncomputable def measureAddress (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (i : I) (x : W→Bool) : ActualY keep L i :=
  ⟨sourceTuple keep L i x,Set.mem_range_self x⟩

set_option maxHeartbeats 4200000 in
omit [Nonempty W] [Fintype F] in
theorem sum_actual_measurements {R : Type*} [CommRing R]
    (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B) (i : I)
    (S : Finset W) (q : (W→Bool)→R) :
    (∑ x : {x : W→Bool // ∀ w∈S,x w=true},q x.val) =
      ∑ y : ActualY keep L i,
        ∑ x : {x : W→Bool // sourceTuple keep L i x=y.val ∧ ∀ w∈S,x w=true},q x.val := by
  let p (x : W→Bool) := ∀ w∈S,x w=true
  let X := {x : W→Bool // p x}
  letI : Fintype X := @Subtype.fintype _ p (fun x=>inferInstanceAs (Decidable (∀ w∈S,x w=true))) _
  let get (x : X) : ActualY keep L i := measureAddress keep L i x.val
  calc
    _ = ∑ x : X,q x.val := rfl
    _ = ∑ y : ActualY keep L i,∑ x : {x : X // get x=y},q x.val.val :=
      (Fintype.sum_fiberwise get (fun x=>q x.val)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      let e : {x : X // get x=y} ≃ {x : W→Bool // sourceTuple keep L i x=y.val ∧ ∀ w∈S,x w=true} :=
        ⟨fun x=>⟨x.val.val,congrArg Subtype.val x.property,x.val.property⟩,
         fun x=>⟨⟨x.val,x.property.2⟩,Subtype.ext x.property.1⟩,
         fun _=>rfl,fun _=>rfl⟩
      exact e.sum_comp (fun x=>q x.val)

set_option maxHeartbeats 12000000 in
theorem same_high_coefficient_as_native_macros
    (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (mark : V↪E) (t : I→ℚ) (M : Mix Copy I B) (hM : ActualBaseInvariant keep L M)
    (P : SourceRecipe L mark) (i : I) (hi : t i≠0) (j : ℕ) (σ : V→Bool) :
    (centerBivar (t i) (actualH L mark t M P σ)).coeff j =
      ∑ a : TaylorList W j,∑ y : ActualY keep L i,
        (-1:ℚ[X])^((a.val.1\a.val.2).card) *
          ((actualMacro keep L mark t M P i a.val.1 a.val.2 y).value σ).coeff j := by
  rw [centered_actualH,finset_sum_coeff]
  simp_rw [actualPatch_small_window]
  rw [assemble_taylor_pairs]
  apply Finset.sum_congr rfl
  intro a _
  have hs := sum_actual_measurements keep L i a.val.1
    (fun x=>(actualPatch L mark t M P i σ x a.val.2).coeff j)
  rw [hs,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [actualMacro_value keep L mark t M hM P i hi,finset_sum_coeff]

omit [Nonempty W] in
noncomputable def projectedMacro (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (mark : V↪E) (t : I→ℚ) (M : Mix Copy I B)
    (P : SourceRecipe L mark) (i : I) (J ell : ℕ) (S U : Finset W)
    (y : ActualY keep L i) :
    GroupProducts.GroupTerm (pinWord L mark) (P5A2.Double ℚ ell J) where
  coordinate := i
  coeff := 1
  factor g b := jetImage ell J ((actualMacro keep L mark t M P i S U y).factor g b)

omit [Nonempty W] in
theorem projectedMacro_value (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (mark : V↪E) (t : I→ℚ) (M : Mix Copy I B)
    (P : SourceRecipe L mark) (i : I) (J ell : ℕ) (S U : Finset W)
    (y : ActualY keep L i) (σ : V→Bool) :
    (projectedMacro keep L mark t M P i J ell S U y).value σ =
      jetImage ell J ((actualMacro keep L mark t M P i S U y).value σ) := by
  unfold GroupProducts.GroupTerm.value
  change 1*(∏ g,jetImage ell J ((actualMacro keep L mark t M P i S U y).factor g (fun v=>σ v.val)))=
    jetImage ell J (1*(∏ g,(actualMacro keep L mark t M P i S U y).factor g (fun v=>σ v.val)))
  simp only [one_mul,map_prod]

set_option maxHeartbeats 12000000 in
/-- No caller-provided low-rank premise. This bound follows from the
actual physical coefficients, after gathering in the real z,V register. -/
theorem actual_native_order_rank_upper [Fintype V] [DecidableEq V]
    (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (mark : V↪E) (t : I→ℚ) (M : Mix Copy I B) (hM : ActualBaseInvariant keep L M)
    (P : SourceRecipe L mark) (S : I→Finset B) (i : I) (hi : t i≠0) (j ell : ℕ)
    (s : Fin ell) :
    cutLength (EmpiricalCutMoments.labelCut (MainIncidence.labels mark (realCell L)) id S i)
      (fun σ=>nativeCoeff (trimV ell (actualH L mark t M P σ)) (t i) j s) ≤
      (TaylorList W j).card * Fintype.card (ActualY keep L i) * (ell*(j+1)) := by
  have hell : 0<ell := Nat.zero_lt_of_lt s.isLt
  let A := TaylorList W j × ActualY keep L i
  let term (a : A) := projectedMacro keep L mark t M P i (j+1) ell a.1.val.1 a.1.val.2 a.2
  let read (a : A) : P5A2.Double ℚ ell (j+1)→ₗ[ℚ]ℚ :=
    ((-1:ℚ)^((a.1.val.1\a.1.val.2).card)) •
      (P5A2.pairBasis ell (j+1) hell).coord (s,⟨j,Nat.lt_succ_self _⟩)
  rw [signs_own_factor_word]
  apply native_order_rank_upper (pinWord L mark) S i j ell hell term (fun _=>rfl) read
  intro σ
  rw [native_coeff_trim]
  unfold nativeCoeff
  rw [same_high_coefficient_as_native_macros keep L mark t M hM P i hi,finset_sum_coeff,Fintype.sum_prod_type]
  simp only [finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro y _
  unfold read term
  rw [LinearMap.smul_apply,projectedMacro_value,jetImage_exact_coefficient]
  have hn : C ((-1:ℚ)^((a.val.1\a.val.2).card))=(-1:ℚ[X])^((a.val.1\a.val.2).card) := by simp
  rw [←hn,coeff_C_mul,smul_eq_mul]

#print axioms sum_actual_measurements
#print axioms same_high_coefficient_as_native_macros
#print axioms projectedMacro_value
#print axioms actual_native_order_rank_upper
end P5MainBalance.M6
