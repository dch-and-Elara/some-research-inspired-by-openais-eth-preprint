import MainIncidence
import P5MainIteratorScopes

/-! Actual MAIN full-cell addresses, projection onto a marked pin's
factor word, and the precise separate pin-sign balance threshold. -/
namespace P5MainBalance
open scoped BigOperators Classical

variable {E V U F Copy I B : Type*} [Fintype E] [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype B] [LinearOrder B]

def words : P5MainIterator.WordCell I B ≃ ((I→B) × (I→B)) where
  toFun u := (fun i=> (u i).1,fun i=> (u i).2)
  invFun u i := (u.1 i,u.2 i)
  left_inv u := by funext i; exact Prod.eta _
  right_inv u := by cases u; rfl

def realCell (L : P5MainIterator.SourceLayout E U F Copy I B) (e : E) :
    (I→B) × (I→B) := words (L.placement.slot e).2

def pinWord (L : P5MainIterator.SourceLayout E U F Copy I B) (mark : V ↪ E)
    (v : V) : I→B := L.d (L.factor (mark v))

omit [Fintype E] [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I] [Fintype B] in
theorem signs_own_factor_word (L : P5MainIterator.SourceLayout E U F Copy I B)
    (mark : V ↪ E) : MainIncidence.labels mark (realCell L)=pinWord L mark := by
  funext v i
  exact L.second (mark v) i

omit [Fintype V] [DecidableEq V] [DecidableEq I] [Fintype B] in
theorem cell_load_pullback (L : P5MainIterator.SourceLayout E U F Copy I B)
    (w : (I→B) × (I→B)) :
    SourceDensity.fiberCount (realCell L) w =
      P5MainIterator.cellLoad L (words.symm w) := by
  unfold SourceDensity.fiberCount P5MainIterator.cellLoad
  apply congrArg Finset.card
  ext e
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,realCell]
  exact words.apply_eq_iff_eq_symm_apply

omit [Fintype V] [DecidableEq V] in
theorem real_cell_cap (L : P5MainIterator.SourceLayout E U F Copy I B)
    (h : ∀ u, P5MainIterator.cellLoad L u * Fintype.card (P5MainIterator.WordCell I B)≤2*Fintype.card E)
    : ∀ w, (SourceDensity.fiberCount (realCell L) w:ℚ) ≤
      2*Fintype.card E/(Fintype.card ((I→B) × (I→B)):ℚ) := by
  intro w
  letI : Nonempty ((I→B) × (I→B)) := ⟨w⟩
  have hpos : 0<(Fintype.card ((I→B) × (I→B)):ℚ) :=
    by exact_mod_cast (Fintype.card_pos : 0<Fintype.card ((I→B) × (I→B)))
  apply (le_div_iff₀ hpos).mpr
  rw [cell_load_pullback,←Fintype.card_congr (words (I:=I) (B:=B))]
  exact_mod_cast h (words.symm w)

section Balance
variable [Nonempty V] [Nonempty I] [Nonempty B]

omit [Nonempty I] [DecidableEq V] in
theorem physical_factor_density
    (L : P5MainIterator.SourceLayout E U F Copy I B) (mark : V ↪ E) (C : ℕ)
    (hports : 2*Fintype.card E≤C*Fintype.card V)
    (hcap : ∀ u, P5MainIterator.cellLoad L u * Fintype.card (P5MainIterator.WordCell I B)≤2*Fintype.card E)
    (d : I→B) :
    EmpiricalCutMoments.empiricalLaw (pinWord L mark) d ≤
      C * ProductVariance.uniformWeight (I→B) := by
  rw [←signs_own_factor_word]
  exact MainIncidence.project_marked_incidence mark (realCell L) C hports
    (real_cell_cap L hcap) Prod.snd _ MainIncidence.factor_word_fiber d

omit [Nonempty I] [DecidableEq V] in
theorem actual_symbol_mass_cap
    (L : P5MainIterator.SourceLayout E U F Copy I B) (mark : V ↪ E) (C : ℕ)
    (hports : 2*Fintype.card E≤C*Fintype.card V)
    (hcap : ∀ u, P5MainIterator.cellLoad L u * Fintype.card (P5MainIterator.WordCell I B)≤2*Fintype.card E)
    (t : I) (a : B) :
    EmpiricalCutMoments.empiricalLaw (fun v => pinWord L mark v t) a ≤
      C * ProductVariance.uniformWeight B := by
  rw [←signs_own_factor_word]
  exact MainIncidence.project_marked_incidence mark (realCell L) C hports
    (real_cell_cap L hcap) (fun c=>c.2 t) _ (MainIncidence.factor_symbol_fiber t) a

omit [Nonempty I] [DecidableEq V] in
theorem complete_pin_sign_balance
    (L : P5MainIterator.SourceLayout E U F Copy I B) (mark : V ↪ E) (C : ℕ)
    (hports : 2*Fintype.card E≤C*Fintype.card V)
    (hcap : ∀ u, P5MainIterator.cellLoad L u * Fintype.card (P5MainIterator.WordCell I B)≤2*Fintype.card E)
    (hA : 4*C≤3*Fintype.card B) :
    ∃ S : I→Finset B, ∀ t, (1/4:ℚ)*Fintype.card V ≤
      (min (EmpiricalCutMoments.labelCut (pinWord L mark) id S t).card
        (Fintype.card V-(EmpiricalCutMoments.labelCut (pinWord L mark) id S t).card) : ℕ) := by
  have hp : 0<(Fintype.card B:ℚ) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card B)
  have hCb : C*ProductVariance.uniformWeight B ≤ (3/4:ℚ) := by
    rw [ProductVariance.uniformWeight,←div_eq_mul_inv]
    apply (div_le_iff₀ hp).mpr
    have H : 4*(C:ℚ)≤3*(Fintype.card B:ℚ) := by exact_mod_cast hA
    linarith only [H]
  choose S hS using fun i => BalancedUnion.exists_balanced_vertex_union_of_law
    (fun v=>pinWord L mark v i) (fun a => (actual_symbol_mass_cap L mark C hports hcap i a).trans hCb)
  exact ⟨S,hS⟩

/-- The original graph cut is on the un-cloned sign vertices. The actual
port type and source variable word may be on a separate cloned set. -/
def layoutFromPhysical
    (L : P5MainIterator.SourceLayout E U F Copy I B) (mark : V ↪ E)
    (G : Finset (V×V)) (C : ℕ)
    (hC : 0<C) (hports : 2*Fintype.card E≤C*Fintype.card V)
    (hcap : ∀ u, P5MainIterator.cellLoad L u * Fintype.card (P5MainIterator.WordCell I B)≤2*Fintype.card E)
    (hA : 4*C≤3*Fintype.card B) (hloop : ∀ v,(v,v)∉G)
    (hreg : ∀ v,GraphCutMoments.degree G v=3) (γ : ℚ) (hγ : 0<γ) (hγ1 : γ≤1)
    (hexp : ∀ U : Finset V, γ*(min U.card (Fintype.card V-U.card) : ℕ)≤
      ((GraphCutMoments.boundary G U).card:ℚ)) :
    MainIncidence.Layout G mark (realCell L) C where
  positive := hC
  ports := hports
  maxLoad := real_cell_cap L hcap
  alphabet := hA
  loopless := hloop
  regular := hreg
  gamma := γ
  gamma_pos := hγ
  gamma_le_one := hγ1
  expansion := hexp

end Balance

#print axioms signs_own_factor_word
#print axioms cell_load_pullback
#print axioms real_cell_cap
#print axioms physical_factor_density
#print axioms actual_symbol_mass_cap
#print axioms complete_pin_sign_balance
#print axioms layoutFromPhysical
end P5MainBalance
