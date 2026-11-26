import P5FrontendG1TannerIncidence
import P5FrontendG1TannerPolynomial
import P5FrontendG1TannerAsymptotic

/-! The original G1 two-sided ownership failure and the necessary appended
row count on cover inputs. No claims about numerical comparison bits,
row-vector distinctness, group separation, or the cost of greedy choices. -/
namespace Paper5.FrontendG1.Tanner
open Paper5.NativeEntry Paper5.FrontendG1.Normalization

section ActualPolynomials
variable {V : Type*} [Fintype V] [DecidableEq V] {E : Finset (V×V)}

def PinFlips (E : Finset (V×V)) (sgn : V→Bool) (w : GuardIndex E→F₂) (v : V) : Prop :=
  let s' := Function.update sgn v (!sgn v)
  (rowPoly E s' w).coeff (exponent (zMon v)) ≠ (rowPoly E sgn w).coeff (exponent (zMon v)) ∧
  (rowPoly E s' w).coeff (exponent (zxMon v))=1 ∧ (rowPoly E sgn w).coeff (exponent (zxMon v))=1

theorem concrete_two_row_sign_dependence {B : ℕ} (P : PrintedInput (GuardIndex E) B)
    (hB : 0<B) (hm : 0<Fintype.card (GuardIndex E))
    (hq : 1<sourceQ B (Fintype.card (GuardIndex E))) (sgn : V→Bool) (v : V) :
    ∃ j : Fin (sourceLocalRows B (Fintype.card (GuardIndex E))),
      let r₁ : PrintRows B (Fintype.card (GuardIndex E)) := .inl ((P.kept (pinIndex v)).1,j)
      let r₂ : PrintRows B (Fintype.card (GuardIndex E)) :=
        .inr (rightEndpoint P.shifts (P.kept (pinIndex v)),j)
      r₁≠r₂ ∧ PinFlips E sgn (P.initial r₁) v ∧ PinFlips E sgn (P.initial r₂) v := by
  obtain ⟨j,hn,hL,hR⟩ := printed_opposite_endpoints P hB hm hq (pinIndex v)
  exact ⟨j,hn,sign_flip_preserves_quadratic E sgn _ v hL,
    sign_flip_preserves_quadratic E sgn _ v hR⟩

theorem concrete_row_many_dependent_signs {B : ℕ} (P : PrintedInput (GuardIndex E) B)
    (hB : 0<B) (hm : 0<Fintype.card (GuardIndex E))
    (hq : 1<sourceQ B (Fintype.card (GuardIndex E)))
    (hC : ∀v,GraphCutMoments.degree E v=3) (sgn : V→Bool) :
    ∃ r : PrintRows B (Fintype.card (GuardIndex E)),
      4*B<7*(signsRead P.initial r).card ∧
      ∀ v ∈ signsRead P.initial r, PinFlips E sgn (P.initial r) v := by
  obtain ⟨r,hr⟩ := printed_some_row_many_signs P hB hm hq hC
  refine ⟨r,hr,?_⟩
  intro v hv
  exact sign_flip_preserves_quadratic E sgn _ v (Finset.mem_filter.mp hv).2
end ActualPolynomials

def appendRows {C R : Type*} {j : ℕ} (A : Matrix R C F₂) (next : Matrix (Fin j) C F₂) :
    Matrix (R⊕Fin j) C F₂ := Sum.elim A next

theorem append_keeps_prefix {C R : Type*} {j : ℕ} (A : Matrix R C F₂)
    (next : Matrix (Fin j) C F₂) (r : R) (i : C) :
    appendRows A next (.inl r) i=A r i := rfl

section Required
variable {V R : Type*} [Fintype V] [Fintype R] [DecidableEq V] {E : Finset (V×V)}

theorem exact_one_requires_many_appended {j : ℕ} (A : Matrix R (GuardIndex E) F₂)
    (extra : Matrix (Fin j) (GuardIndex E) F₂) (sgn : V→Bool)
    (hCount : literalHashedCount (appendRows A extra) sgn=1) :
    Fintype.card V-Fintype.card R≤j := by
  have hRank : Fintype.card V≤(appendRows A extra).rank := by
    by_contra! hh
    have he := literal_early_even (appendRows A extra) sgn hh
    rw [hCount] at he
    exact (by decide : ¬2 ∣ (1:ℕ)) he
  have hHi := Matrix.rank_le_card_height (appendRows A extra)
  simp only [Fintype.card_sum,Fintype.card_fin] at hHi
  omega

theorem source_B_at_least_seven (s : ℕ) (hs : 2≤s) : 7≤sparB₂ s hs := by
  have hM := actual_source_M_gt_four s hs
  change 4<2^(sparExponent s hs) at hM
  unfold sparB₂
  omega

omit [Fintype R] in
theorem concrete_requires_half_appends {B j : ℕ} (P : PrintedInput (GuardIndex E) B)
    (extra : Matrix (Fin j) (GuardIndex E) F₂) (sgn : V→Bool)
    (hB : 7≤B) (hm : 0<Fintype.card (GuardIndex E))
    (hq : 1<sourceQ B (Fintype.card (GuardIndex E)))
    (hC : ∀v,GraphCutMoments.degree E v=3)
    (hCover : PinnedCNF.AllEdges E sgn)
    (hExact : literalHashedCount (appendRows P.initial extra) sgn =
      familyCount (parsed (guardedFormula E sgn))) :
    Fintype.card V≤2*j := by
  have hOne : literalHashedCount (appendRows P.initial extra) sgn=1 := by
    rw [hExact,parsed_count,guarded_count_indicator,if_pos hCover]
  have hh := exact_one_requires_many_appended P.initial extra sgn hOne
  have hPrefix := printed_initial_small_prefix (C:=GuardIndex E) (by omega : 0<B) hm hq
  have hM := guard_index_cubic E hC
  have h7 := Nat.mul_le_mul_left (Fintype.card (PrintRows B (Fintype.card (GuardIndex E)))) hB
  omega
end Required

universe u
/-- Original cubic guard size along any actual graphs: the number of
initial rows is o(N), written as every fixed positive integer multiple
being smaller than N eventually. This does not assert graph existence. -/
theorem eventual_guarded_prefix_small (K : ℕ) :
    ∃ N₀ : ℕ, ∀ {U : Type u} [Fintype U] [DecidableEq U]
      (E : Finset (U×U)), (∀ v, GraphCutMoments.degree E v=3) →
      N₀≤Fintype.card U →
      ∃ hs : 2≤printedGroups (Fintype.card (GuardVar U)),
        let B := sparB₂ (printedGroups (Fintype.card (GuardVar U))) hs
        let m := Fintype.card (GuardIndex E)
        7≤B ∧ 1<sourceQ B m ∧ K*Fintype.card (PrintRows B m)<Fintype.card U := by
  obtain ⟨n₀,hN⟩ := actual_printed_large_tanner (4*K)
  refine ⟨max 1 n₀,?_⟩
  intro U _ _ E hC hN₀
  let N := Fintype.card U
  let n := Fintype.card (GuardVar U)
  let m := Fintype.card (GuardIndex E)
  have hn : n=2*N := guarded_variable_card
  have hm : 2*m=7*N := guard_index_cubic E hC
  have hn₀ : n₀≤n := by
    have hh := (le_max_right 1 n₀).trans hN₀
    change n₀≤N at hh
    omega
  have hm0 : 0<m := by
    have hh := (le_max_left 1 n₀).trans hN₀
    change 1≤N at hh
    omega
  obtain ⟨hs,hB,hq⟩ := hN n hn₀ m (by omega) (by omega)
  let B := sparB₂ (printedGroups n) hs
  let a := Fintype.card (PrintRows B m)
  have hB7 := source_B_at_least_seven _ hs
  have hPrefix : a*B<m := printed_initial_small_prefix (C:=GuardIndex E) (by omega) hm0 hq
  have h4 : a*(4*K)≤a*B := Nat.mul_le_mul_left a hB
  have he : a*(4*K)=4*(K*a) := by ring
  refine ⟨hs,hB7,hq,?_⟩
  change K*a<N
  omega

#print axioms concrete_two_row_sign_dependence
#print axioms concrete_row_many_dependent_signs
#print axioms append_keeps_prefix
#print axioms exact_one_requires_many_appended
#print axioms source_B_at_least_seven
#print axioms concrete_requires_half_appends
#print axioms eventual_guarded_prefix_small
end Paper5.FrontendG1.Tanner