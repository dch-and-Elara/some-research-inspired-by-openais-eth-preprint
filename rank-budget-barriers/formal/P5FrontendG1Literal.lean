import P5FrontendG1Rank
import PinnedCNF

/-! The three actual clause kinds in Pro v7 G1. This module links the rank
arithmetic to the source formula on exactly 2N bits; it does not assert that
any particular global Tanner or greedy tie-break behaves in a fixed way. -/
namespace Paper5.FrontendG1
open scoped BigOperators

abbrev GuardVar (V : Type*) := V ⊕ V
abbrev GuardIndex {V : Type*} (E : Finset (V×V)) := V ⊕ (V ⊕ ↥E)

variable {V : Type*} [DecidableEq V]

def guardedClause (E : Finset (V×V)) (sgn : V→Bool) :
    GuardIndex E→Std.Sat.CNF.Clause (GuardVar V)
  | .inl v => [(.inr v,true)]
  | .inr (.inl v) => [(.inr v,false),(.inl v,sgn v)]
  | .inr (.inr e) => [(.inl e.val.1,true),(.inl e.val.2,true)]

noncomputable def guardedFormula [Fintype V] (E : Finset (V×V)) (sgn : V→Bool) :
    Std.Sat.CNF (GuardVar V) :=
  (Finset.univ : Finset (GuardIndex E)).toList.map (guardedClause E sgn)

omit [DecidableEq V] in
theorem guarded_length [Fintype V] (E : Finset (V×V)) (sgn : V→Bool) :
    (guardedFormula E sgn).length=2*Fintype.card V+E.card := by
  simp [guardedFormula,GuardIndex,Nat.two_mul]
  omega

def guardTerms (E : Finset (V×V)) (sgn : V→Bool) :
    GuardIndex E→List (Finset (GuardVar V))
  | .inl v => [∅,{.inr v}]
  | .inr (.inl v) => [{.inr v,.inl v}] ++ (if sgn v then [{.inr v}] else [])
  | .inr (.inr e) => [∅,{.inl e.val.1},{.inl e.val.2},{.inl e.val.1,.inl e.val.2}]

theorem guard_terms_small (E : Finset (V×V)) (sgn : V→Bool)
    (i : GuardIndex E) (t : Finset (GuardVar V)) (h : t∈guardTerms E sgn i) :
    t.card≤2 := by
  rcases i with v|(v|e)
  · simp [guardTerms] at h
    rcases h with rfl|rfl <;> simp
  · cases hs : sgn v <;> simp [guardTerms,hs] at h
    · subst t
      exact Finset.card_insert_le _ _
    · rcases h with rfl|rfl
      · exact Finset.card_insert_le _ _
      · simp
  · simp [guardTerms] at h
    rcases h with rfl|rfl|rfl|rfl
    · simp
    · simp
    · simp
    · exact Finset.card_insert_le _ _

def guardQuad (E : Finset (V×V)) (sgn : V→Bool) (i : GuardIndex E) : Quad (GuardVar V) :=
  ⟨guardTerms E sgn i,fun t h=>guard_terms_small E sgn i t h⟩

def wordOfMask {W : Type*} [DecidableEq W] (x : Finset W) : W→Bool :=
  fun v=>decide (v∈x)

def zBit (b : Bool) : F₂ := if b then 1 else 0

def literalViolation (E : Finset (V×V)) (sgn : V→Bool) (a : GuardVar V→Bool) :
    GuardIndex E→F₂ :=
  fun i=>if (guardedClause E sgn i).eval a then 0 else 1

theorem quad_is_literal_violation (E : Finset (V×V)) (sgn : V→Bool)
    (x : Finset (GuardVar V)) (i : GuardIndex E) :
    (guardQuad E sgn i).eval x = literalViolation E sgn (wordOfMask x) i := by
  rcases i with v|(v|e)
  · by_cases hz : Sum.inr v∈x
    all_goals simp [guardQuad,guardedClause,guardTerms,Quad.eval,mon,literalViolation,wordOfMask,hz]
    all_goals decide
  · cases hs : sgn v
    all_goals by_cases hz : Sum.inr v∈x
    all_goals by_cases hx : Sum.inl v∈x
    all_goals simp [guardQuad,guardedClause,guardTerms,Quad.eval,mon,literalViolation,wordOfMask,Finset.insert_subset_iff,hs,hz,hx]
    all_goals decide
  · by_cases hu : Sum.inl e.val.1∈x
    all_goals by_cases hv : Sum.inl e.val.2∈x
    all_goals simp [guardQuad,guardedClause,guardTerms,Quad.eval,mon,literalViolation,wordOfMask,Finset.insert_subset_iff,hu,hv]
    all_goals decide

omit [DecidableEq V] in
theorem guarded_sat_iff [Fintype V] (E : Finset (V×V)) (sgn : V→Bool) (a : GuardVar V→Bool) :
    (guardedFormula E sgn).Sat a ↔
      a=Sum.elim sgn (fun _=>true) ∧ PinnedCNF.AllEdges E sgn := by
  have hEval : (guardedFormula E sgn).Sat a ↔
      ∀ i : GuardIndex E,(guardedClause E sgn i).eval a=true := by
    simp [Std.Sat.CNF.sat_def,guardedFormula,Std.Sat.CNF.eval,List.all_eq_true]
  rw [hEval]
  constructor
  · intro h
    have hz (v : V) : a (.inr v)=true := by simpa [guardedClause] using h (.inl v)
    have hx (v : V) : a (.inl v)=sgn v := by simpa [guardedClause,hz] using h (.inr (.inl v))
    constructor
    · funext v
      cases v with
      | inl w => exact hx w
      | inr w => exact hz w
    · intro e he
      simpa [guardedClause,hx] using h (.inr (.inr ⟨e,he⟩))
  · rintro ⟨he,hCover⟩ i
    subst a
    rcases i with v|(v|e)
    · simp [guardedClause]
    · simp [guardedClause]
    · simpa [guardedClause] using hCover e.val e.property

omit [DecidableEq V] in
theorem guarded_count_indicator [Fintype V] (E : Finset (V×V)) (sgn : V→Bool) :
    PinnedCNF.modelCount (guardedFormula E sgn)=(open scoped Classical in if PinnedCNF.AllEdges E sgn then 1 else 0) := by
  classical
  calc
    _ = (if PinnedCNF.AllEdges E sgn then ({Sum.elim sgn (fun _=>true)} :
        Finset (GuardVar V→Bool)) else ∅).card := by
      unfold PinnedCNF.modelCount
      apply congrArg Finset.card
      ext a
      by_cases hc : PinnedCNF.AllEdges E sgn <;>
        simp [←Std.Sat.CNF.sat_def,guarded_sat_iff,hc]
    _ = _ := by split_ifs <;> simp

def maskEquiv (W : Type*) [Fintype W] [DecidableEq W] : Finset W ≃ (W→Bool) where
  toFun := wordOfMask
  invFun f := Finset.univ.filter fun v=> f v=true
  left_inv x := by ext v; simp [wordOfMask]
  right_inv f := by funext v; cases h : f v <;> simp [wordOfMask,h]

noncomputable def literalHashedCount [Fintype V] {R : Type*} {E : Finset (V×V)}
    (A : Matrix R (GuardIndex E) F₂) (sgn : V→Bool) : ℕ :=
  Nat.card {a : GuardVar V→Bool // A.mulVec (literalViolation E sgn a)=0}

theorem literal_hashed_equals_polynomial [Fintype V] {R : Type*} [Fintype R] {E : Finset (V×V)}
    (A : Matrix R (GuardIndex E) F₂) (sgn : V→Bool) :
    literalHashedCount A sgn=hashedCount A (guardQuad E sgn) := by
  classical
  have h (x : Finset (GuardVar V)) : violations (guardQuad E sgn) x =
      literalViolation E sgn (maskEquiv (GuardVar V) x) := by
    funext i
    exact quad_is_literal_violation E sgn x i
  let S := Finset.univ.filter (fun x : Finset (GuardVar V)=>A.mulVec (violations (guardQuad E sgn) x)=0)
  let er : ↥S ≃ {x : Finset (GuardVar V) // A.mulVec (violations (guardQuad E sgn) x)=0} :=
    Equiv.subtypeEquivRight (by simp [S])
  let e : {x : Finset (GuardVar V) // A.mulVec (violations (guardQuad E sgn) x)=0} ≃
      {a : GuardVar V→Bool // A.mulVec (literalViolation E sgn a)=0} :=
    Equiv.subtypeEquiv (maskEquiv (GuardVar V)) (fun x => by rw [h])
  change Nat.card {a : GuardVar V→Bool // A.mulVec (literalViolation E sgn a)=0}=S.card
  rw [Nat.card_congr (er.trans e).symm,Nat.card_eq_fintype_card,Fintype.card_coe]

theorem literal_early_divisibility [Fintype V] {R : Type*} [Fintype R] {E : Finset (V×V)}
    (A : Matrix R (GuardIndex E) F₂) (sgn : V→Bool) :
    (2:ℕ)^(Fintype.card V-A.rank) ∣ literalHashedCount A sgn := by
  rw [literal_hashed_equals_polynomial]
  exact quadratic_hash_rank_divisible A (guardQuad E sgn) (Fintype.card V)
    (by simp [GuardVar,Nat.two_mul])

theorem literal_early_even [Fintype V] {R : Type*} [Fintype R] {E : Finset (V×V)}
    (A : Matrix R (GuardIndex E) F₂) (sgn : V→Bool) (h : A.rank<Fintype.card V) :
    2∣literalHashedCount A sgn := by
  rw [literal_hashed_equals_polynomial]
  exact early_hash_even A (guardQuad E sgn) (Fintype.card V)
    (by simp [GuardVar,Nat.two_mul]) h

theorem literal_correct_final_requires_appends [Fintype V] {E : Finset (V×V)} {a j : ℕ}
    (A : Matrix (Fin (a+j)) (GuardIndex E) F₂) (sgn : V→Bool)
    (hCover : PinnedCNF.AllEdges E sgn)
    (hExact : literalHashedCount A sgn=PinnedCNF.modelCount (guardedFormula E sgn)) :
    Fintype.card V-a≤j := by
  refine one_count_requires_appends A (guardQuad E sgn) (Fintype.card V)
    (by simp [GuardVar,Nat.two_mul]) ?_
  rw [←literal_hashed_equals_polynomial,hExact,guarded_count_indicator,if_pos hCover]

/-- The appended-row lower bound enters the actual source numerical guard
without a limit argument: B ≥ 7 and a B < m = 7N/2 suffice. -/
theorem literal_tanner_prefix_half_append [Fintype V] {E : Finset (V×V)}
    {a j B : ℕ} (A : Matrix (Fin (a+j)) (GuardIndex E) F₂) (sgn : V→Bool)
    (hCover : PinnedCNF.AllEdges E sgn)
    (hExact : literalHashedCount A sgn=PinnedCNF.modelCount (guardedFormula E sgn))
    (hCubic : 2*E.card=3*Fintype.card V) (hB : 7≤B)
    (hInitial : a*B<(guardedFormula E sgn).length) :
    Fintype.card V≤2*j := by
  have hr := literal_correct_final_requires_appends A sgn hCover hExact
  have hM := guarded_length E sgn
  have hab := Nat.mul_le_mul_left a hB
  omega

#print axioms guarded_length
#print axioms guard_terms_small
#print axioms quad_is_literal_violation
#print axioms guarded_sat_iff
#print axioms guarded_count_indicator
#print axioms literal_hashed_equals_polynomial
#print axioms literal_early_divisibility
#print axioms literal_early_even
#print axioms literal_correct_final_requires_appends
#print axioms literal_tanner_prefix_half_append
end Paper5.FrontendG1