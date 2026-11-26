import P5AlwaysSatOriginalCNF
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! Exact assignments, cardinality and parity of the literal §4.5 formula.
The y=0 model set is an injectively encoded Boolean choice times a powerset;
y=1 contributes only the fixed tuple when the old signs cover the graph. -/
namespace Paper5.AlwaysSatOriginal
open scoped BigOperators

variable {V : Type*} {T : Finset V}

def activeBonus (T : Finset V) (s : V→Bool) : Finset ↥T :=
  Finset.univ.filter fun v=>s v.val=true

noncomputable def maskOf {W : Type*} (A : Finset W) (w : W) : Bool := by
  classical
  exact decide (w∈A)

noncomputable def zeroCode (T : Finset V) (s : V→Bool) (p : Bool×Finset ↥T) : Var T→Bool :=
  assignment T s false p.1 (maskOf p.2)

theorem zero_code_injective (T : Finset V) (s : V→Bool) : Function.Injective (zeroCode T s) := by
  classical
  intro p q h
  apply Prod.ext
  · exact congrFun h (b₀ T)
  · ext v
    have hh := congrFun h (bonus v)
    simp only [zeroCode,assignment_bonus,maskOf] at hh
    by_cases hp : v∈p.2 <;> by_cases hq : v∈q.2 <;> simp_all

noncomputable def zeroModels (T : Finset V) (s : V→Bool) : Finset (Var T→Bool) := by
  classical
  exact ((Finset.univ : Finset Bool) ×ˢ (activeBonus T s).powerset).image (zeroCode T s)

theorem zero_models_mem (T : Finset V) (s : V→Bool) (a : Var T→Bool) :
    a∈zeroModels T s ↔ a (y T)=false ∧ fixedPins T s a ∧ bonusAllowed T s a := by
  classical
  rw [zeroModels,Finset.mem_image]
  constructor
  · rintro ⟨p,hp,rfl⟩
    have hSub := Finset.mem_powerset.mp (Finset.mem_product.mp hp).2
    refine ⟨rfl,fun v=>rfl,?_⟩
    intro v hv
    have hh : v∈p.2 := by simpa [zeroCode,maskOf] using hv
    exact (Finset.mem_filter.mp (hSub hh)).2
  · rintro ⟨hy,hp,hb⟩
    let M : Finset ↥T := Finset.univ.filter fun v=>a (bonus v)=true
    have hM : M⊆activeBonus T s := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb v (Finset.mem_filter.mp hv).2⟩
    refine ⟨(a (b₀ T),M),Finset.mem_product.mpr
      ⟨Finset.mem_univ _,Finset.mem_powerset.mpr hM⟩,?_⟩
    funext w
    rcases w with v|(c|v)
    · exact (hp v).symm
    · cases c
      · exact hy.symm
      · rfl
    · change maskOf M v=a (bonus v)
      cases hv : a (bonus v) <;> simp [maskOf,M,hv]

noncomputable def oneModels (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    Finset (Var T→Bool) := by
  classical
  exact if PinnedCNF.AllEdges E s then {assignment T s true false (fun _=>false)} else ∅

theorem one_models_mem (E : Finset (V×V)) (T : Finset V) (s : V→Bool) (a : Var T→Bool) :
    a∈oneModels E T s ↔ a (y T)=true ∧ fixedPins T s a ∧
      PinnedCNF.AllEdges E s ∧ allBonusesZero T a := by
  classical
  by_cases hc : PinnedCNF.AllEdges E s
  · rw [oneModels,if_pos hc,Finset.mem_singleton]
    constructor
    · rintro rfl
      simp [fixedPins,allBonusesZero,hc]
    · rintro ⟨hy,hp,_,hb⟩
      funext w
      rcases w with v|(c|v)
      · exact hp v
      · cases c
        · exact hy
        · exact hb.1
      · exact hb.2 v
  · simp [oneModels,hc]

noncomputable def sourceModels [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    Finset (Var T→Bool) := by
  classical
  exact (Finset.univ : Finset (Var T→Bool)).filter fun a=>(formula E T s).eval a=true

theorem source_models_eq [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    sourceModels E T s=zeroModels T s∪oneModels E T s := by
  classical
  ext a
  simp only [sourceModels,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,
    ←Std.Sat.CNF.sat_def,sat_iff_branches,zero_models_mem,one_models_mem]
  cases hy : a (y T) <;> simp

theorem source_model_parts_disjoint (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    Disjoint (zeroModels T s) (oneModels E T s) := by
  refine Finset.disjoint_left.mpr ?_
  intro a hz ho
  exact Bool.false_ne_true (((zero_models_mem T s _).mp hz).1.symm.trans
    ((one_models_mem E T s _).mp ho).1)

theorem zero_models_card (T : Finset V) (s : V→Bool) :
    (zeroModels T s).card=2^(1+(activeBonus T s).card) := by
  classical
  rw [zeroModels,Finset.card_image_of_injective _ (zero_code_injective T s)]
  simp [pow_add]

noncomputable def coverBit (E : Finset (V×V)) (s : V→Bool) : ℕ := by
  classical
  exact if PinnedCNF.AllEdges E s then 1 else 0

theorem cover_bit_le_one (E : Finset (V×V)) (s : V→Bool) : coverBit E s≤1 := by
  unfold coverBit
  split_ifs <;> decide

theorem one_models_card (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    (oneModels E T s).card=coverBit E s := by
  classical
  by_cases hc : PinnedCNF.AllEdges E s <;> simp [oneModels,coverBit,hc]

theorem active_bonus_card (T : Finset V) (s : V→Bool) :
    (activeBonus T s).card=(T.filter fun v=>s v=true).card := by
  classical
  let e : ↥T↪V := ⟨Subtype.val,Subtype.val_injective⟩
  have hMap : (activeBonus T s).map e=T.filter (fun v=>s v=true) := by
    ext v
    simp only [activeBonus,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t.property,ht⟩
    · rintro ⟨hv,hs⟩
      exact ⟨⟨v,hv⟩,hs,rfl⟩
  rw [←hMap,Finset.card_map]

theorem active_bonus_sum (T : Finset V) (s : V→Bool) :
    (activeBonus T s).card=∑ v∈T,if s v then (1:ℕ) else 0 := by
  rw [active_bonus_card,Finset.card_filter]

theorem original_model_count [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    PinnedCNF.modelCount (formula E T s)=
      2^(1+(activeBonus T s).card)+coverBit E s := by
  have hModel : PinnedCNF.modelCount (formula E T s)=(sourceModels E T s).card := by
    classical
    unfold PinnedCNF.modelCount sourceModels
    apply congrArg Finset.card
    ext a
    simp
  rw [hModel,source_models_eq,Finset.card_union_of_disjoint (source_model_parts_disjoint E T s),
    zero_models_card,one_models_card]

/-- The exact formula (M.7) with the old pinned graph count as its second term. -/
theorem original_display_M7 [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    PinnedCNF.modelCount (formula E T s)=
      2^(1+∑ v∈T,if s v then (1:ℕ) else 0)+PinnedCNF.modelCount (PinnedCNF.formula E s) := by
  classical
  rw [original_model_count,active_bonus_sum,PinnedCNF.count_eq_indicator]
  rfl

theorem original_count_parity [Fintype V] (E : Finset (V×V)) (T : Finset V) (s : V→Bool) :
    PinnedCNF.modelCount (formula E T s)%2=PinnedCNF.modelCount (PinnedCNF.formula E s) := by
  classical
  rw [original_model_count,Nat.add_mod,PinnedCNF.count_eq_indicator]
  have hEven : 2 ∣ (2:ℕ)^(1+(activeBonus T s).card) := by
    rw [pow_add,pow_one]
    exact dvd_mul_right _ _
  rw [Nat.mod_eq_zero_of_dvd hEven]
  by_cases hc : PinnedCNF.AllEdges E s <;> simp [coverBit,hc]

#print axioms zero_code_injective
#print axioms zero_models_mem
#print axioms one_models_mem
#print axioms source_models_eq
#print axioms source_model_parts_disjoint
#print axioms zero_models_card
#print axioms cover_bit_le_one
#print axioms one_models_card
#print axioms active_bonus_card
#print axioms active_bonus_sum
#print axioms original_model_count
#print axioms original_display_M7
#print axioms original_count_parity
end Paper5.AlwaysSatOriginal