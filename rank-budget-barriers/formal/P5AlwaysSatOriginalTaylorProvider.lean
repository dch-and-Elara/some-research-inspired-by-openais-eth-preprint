import P5AlwaysSatOriginalTaylorEventual

/-! Neither provider chart is an external premise here. The same actual
guarded clone on a supplied cubic expander admits both printed layouts
and gives true high-order register obstructions with one uniform ε. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainBalance P5MainIterator P5MainBalance.M6 Filter Real
open scoped Classical BigOperators

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
variable (E : Finset (V×V)) (T : Finset V)

abbrev DirectProvider :=
  MAINCertificate (I:=ActualI E T) (S:=ActualS E T)
    (portOwner E T) (portFactor E T) (marked E T)

abbrev SparseProvider :=
  MAINCertificate (I:=ActualI E T) (S:=ActualS E T)
    (sparseOwner E T) (sparseFactor E T) (sparseMarked E T)

def DirectProvider.Hard (D : DirectProvider E T) (γ : ℚ) (ε : ℝ) : Prop :=
  PrintedWitness (mainN E T) 54 (directDegree E T) 1 γ ε D.layout
    (directChart D.layout (certificate_layout_owners D) (certificate_layout_factors D)).mark
    (directRecipe D.layout (certificate_layout_owners D) (certificate_layout_factors D))

def SparseProvider.Hard (S : SparseProvider E T) (γ : ℚ) (ε : ℝ) : Prop :=
  PrintedWitness (mainN E T) 54 (sparseDegree E T) (mainN E T+1) γ ε S.layout
    (sparseChart S.layout (certificate_layout_owners S) (certificate_layout_factors S)).mark
    ((sparseInput S.layout (certificate_layout_owners S) (certificate_layout_factors S)).compile (mainN E T+1))

set_option maxHeartbeats 17000000 in
theorem actual_M7_MAIN_M6_uniform (γ : ℚ) (hγ : 0<γ) (hγ1 : γ≤1) :
    ∃ ε : ℝ, 0<ε ∧ ∃ N₀ : ℕ,
      ∀ {V : Type u} [Fintype V] [DecidableEq V] [Nonempty V]
        (E : Finset (V×V)) (T : Finset V),
      N₀≤Fintype.card V → T.card≤Fintype.card V/4 →
      (∀ v,(v,v)∉E) → (∀ v,GraphCutMoments.degree E v=3) →
      (∀ U : Finset V,γ*(min U.card (Fintype.card V-U.card) : ℕ)≤
        ((GraphCutMoments.boundary E U).card:ℚ)) →
      ∃ D : DirectProvider E T, ∃ S : SparseProvider E T,
        DirectProvider.Hard E T D γ ε ∧ SparseProvider.Hard E T S γ ε := by
  obtain ⟨ε,hε,hEv⟩ := eventual_width_three_M7 γ hγ hγ1
  obtain ⟨N₁,h₁⟩ := eventually_atTop.mp hEv
  obtain ⟨N₂,h₂⟩ := uniform_main_and_sparse
  obtain ⟨N₃,h₃⟩ := eventually_atTop.mp main_mesh_eventual
  refine ⟨ε,hε,max N₁ (max N₂ (max N₃ 8)),?_⟩
  intro V _ _ _ G B hN hB hLoop hReg hExp
  obtain ⟨hLow,h₂₃⟩ := max_le_iff.mp hN
  obtain ⟨hMid,h₃₈⟩ := max_le_iff.mp h₂₃
  obtain ⟨hHigh,h8⟩ := max_le_iff.mp h₃₈
  let n := mainN G B
  have hv : Fintype.card V≤n := (main_port_card_lower G B).1
  have hg := h₂ G B hMid hReg hB
  rcases hg with ⟨⟨D⟩,⟨S⟩⟩
  letI : Nonempty (ActualS G B) := ⟨⟨0, (by decide : 0<(72:ℕ)).trans_le
    (h₃ n (hHigh.trans hv)).1⟩⟩
  have cD : PrintedCaps n G D.layout γ := by
    refine ⟨?_,?_,hLoop,hExp⟩
    · intro q
      simpa only [←Nat.card_eq_fintype_card] using certificate_caps_cell D q
    · simpa only [←Nat.card_eq_fintype_card] using certificate_caps_copies D
  have cS : PrintedCaps n G S.layout γ := by
    refine ⟨?_,?_,hLoop,hExp⟩
    · intro q
      simpa only [←Nat.card_eq_fintype_card] using certificate_caps_cell S q
    · simpa only [←Nat.card_eq_fintype_card] using certificate_caps_copies S
  have hh := h₁ n (hLow.trans hv) G B hReg D.layout
    (certificate_layout_owners D) (certificate_layout_factors D) S.layout
    (certificate_layout_owners S) (certificate_layout_factors S)
    rfl h8 hB cD cS
  exact ⟨D,S,hh.1,hh.2⟩

#print axioms actual_M7_MAIN_M6_uniform
end Paper5.AlwaysSatOriginal.Physical.Taylor