import J4R43LiteralOutsideHamming
import J4R43LiteralOutsideScalar

/-! No external integer-height or nonconstant-base premise: both
follow from the original positive extreme kernel and old tables. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4500000
set_option maxRecDepth 2400
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {a : ℕ}
local notation "E" => DWire F
local notation "N" => oldColumnNetwork F reg
variable (P : PhysicalPacking N a (Fin 64))

theorem real_weight_is_one_or_base (P : PhysicalPacking N a (Fin 64)) (t : ℤ) (κ : ℤ) (e : E) (x : Bool) :
    columnArgumentWeight F reg P t κ e x=1 ∨ columnArgumentWeight F reg P t κ e x=1-κ := by
  unfold columnArgumentWeight sourceColumnWeight
  by_cases h : columnHit P t e <;> cases x <;> simp [h,bit]

theorem every_literal_marginal_positive (P : PhysicalPacking N a (Fin 64)) (t κ : ℤ) (hn : κ≤0) (σ : W→Bool) (u : DOld F) :
    0<localColumnValue F reg P t κ σ u := by
  let y := columnWitness F σ
  let J := globalColumnBits N y u
  have flag : oldColumnTruth F reg σ (.inr u) J=true := by
    have H := actual_column_flags_read_only_its_old_port F reg σ u (fun _=>false) y
    have JH : J=(fun p : ColumnArgs F reg u=> Sum.elim (fun _=>false) y p.val) := by
      funext p
      obtain ⟨p,e⟩ := p
      cases p
      · exact nomatch e
      · rfl
    exact (congrArg (oldColumnTruth F reg σ (.inr u)) JH).trans
      (H.trans (witness_satisfies_all_true_old_tables F reg σ u))
  have pos (x : ColumnArgs F reg u→Bool) :
      0<∏ q : ColumnArgs F reg u,columnArgumentWeight F reg P t κ (edge q.val) (x q) := by
    apply Finset.prod_pos
    intro q _
    rcases real_weight_is_one_or_base F reg P t κ (edge q.val) (x q) with h|h
    · rw [h]; omega
    · rw [h]; omega
  unfold localColumnValue
  apply Finset.sum_pos'
  · intro x _
    unfold localColumnTerm
    cases eq : oldColumnTruth F reg σ (.inr u) x
    · simp [eq,bit]
    · simpa [eq,bit] using (pos x).le
  · refine ⟨J,Finset.mem_univ _,?_⟩
    unfold localColumnTerm
    simpa [flag,bit] using pos J

theorem actual_graph_factor_positive (P : PhysicalPacking N a (Fin 64)) (t κ : ℤ) (hn : κ≤0) :
    0<graphFactor F reg P t κ := by
  unfold graphFactor
  apply mul_pos <;> apply Finset.prod_pos <;>
    exact fun _ _=>every_literal_marginal_positive F reg P t κ hn _ _

theorem actual_integer_has_height (P : PhysicalPacking N a (Fin 64)) (σ : W→Bool) :
    |factorizedValue F reg P (((2^a:ℕ):ℤ)-1) (J9FactorBounds.kernel (2^a)) σ|≤
      (2:ℤ)^(7*Fintype.card E) := by
  let L := (2:ℕ)^a
  let M := Fintype.card E
  let t := (L:ℤ)-1
  let κ := J9FactorBounds.kernel L
  let B : Finset E := Finset.univ.filter (columnHit P t)
  have hκ : κ≤0 := J9FactorBounds.kernel_nonpos L
  have hb : 1-κ≤(2:ℤ)^(2*L) := by
    have hL : 1≤L := Nat.succ_le_of_lt (pow_pos (by decide) _)
    have d := J9FactorBounds.kernel_budget L hL
    change 1+|κ|≤_ at d
    rw [abs_of_nonpos hκ] at d
    simpa only [sub_eq_add_neg] using d
  have hk : B.card*(2*L)≤6*M := by
    have h := genuine_extreme_matches_budget P
    rw [Nat.card_eq_fintype_card,real_matched_columns_card] at h
    exact h
  let weight (y : E→Bool) (q : E) := sourceColumnWeight P t κ y q
  have zero (y : E→Bool) (q : E) : 0≤weight y q := by
    rcases real_weight_is_one_or_base F reg P t κ q (y q) with h|h
    · change 0≤columnArgumentWeight F reg P t κ q (y q)
      rw [h]; omega
    · change 0≤columnArgumentWeight F reg P t κ q (y q)
      rw [h]; omega
  have upper (y : E→Bool) (q : E) : weight y q≤(2:ℤ)^(2*L) := by
    rcases real_weight_is_one_or_base F reg P t κ q (y q) with h|h
    · change columnArgumentWeight F reg P t κ q (y q)≤_
      rw [h]
      exact (by omega : 1≤1-κ).trans hb
    · change columnArgumentWeight F reg P t κ q (y q)≤_
      rw [h]
      exact hb
  have whole (y : E→Bool) : (∏ q : E,weight y q)≤(2:ℤ)^(6*M) := by
    have cut : (∏ q∈B,weight y q)=(∏ q : E,weight y q) := by
      apply Finset.prod_subset (Finset.subset_univ _)
      intro q _ no
      have miss : ¬columnHit P t q := fun h=>no (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
      simp [weight,sourceColumnWeight,miss]
    calc
      _ = (∏ q∈B,weight y q) := cut.symm
      _ ≤ ∏ _q∈B,(2:ℤ)^(2*L) :=
        Finset.prod_le_prod (fun q _=>zero y q) (fun q _=>upper y q)
      _ = (2:ℤ)^((2*L)*B.card) := by rw [Finset.prod_const,←pow_mul]
      _ ≤ _ := by
        apply pow_le_pow_right₀ (by decide)
        simpa [Nat.mul_comm] using hk
  let T (y : E→Bool) : ℤ :=
    if originalColumnKeep F reg σ y then ∏ q : E,weight y q else 0
  have Tnon (y : E→Bool) : 0≤T y := by
    unfold T
    split
    · exact Finset.prod_nonneg (fun q _=>zero y q)
    · exact le_rfl
  have Tbound (y : E→Bool) : T y≤(2:ℤ)^(6*M) := by
    unfold T
    split
    · exact whole y
    · positivity
  change |factorizedValue F reg P t κ σ|≤_
  rw [←true_columns_are_independent F reg P t κ σ]
  change |∑ y,T y|≤(2:ℤ)^(7*M)
  rw [abs_of_nonneg (Finset.sum_nonneg (fun y _=>Tnon y))]
  calc
    _ ≤ ∑ _y : E→Bool,(2:ℤ)^(6*M) := Finset.sum_le_sum (fun y _=>Tbound y)
    _ = (2:ℤ)^M*(2:ℤ)^(6*M) := by
      rw [Finset.sum_const,Finset.card_univ,Fintype.card_fun,Fintype.card_bool,nsmul_eq_mul]
      simp [M]
    _ = _ := by rw [←pow_add]; congr 1; omega

#print axioms real_weight_is_one_or_base
#print axioms every_literal_marginal_positive
#print axioms actual_graph_factor_positive
#print axioms actual_integer_has_height
end
end J4R43LiteralOutside

