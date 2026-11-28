import J7PrintedParamsBridge
import J7ToJ8Canonical

/-! # Physical incidence atlas of the four-clone CNF family -/
open scoped BigOperators Classical

namespace J7PrintedParamsGraph
open J7SourceLabels

noncomputable section
set_option maxHeartbeats 1400000

abbrev Index := Option (Fin 3)
abbrev Binary (Pair G : Type*) := G ⊕ (Pin Pair × Index)
abbrev OrdinaryRow (Pair G : Type*) := Binary Pair G × Bool
abbrev OrdinaryWire (Pair G : Type*) := OrdinaryRow Pair G × Bool
abbrev OldNonPrivate (Pair G : Type*) := Binary Pair G ⊕ (Pin Pair × Fin 3)

private def indexChart : Index ≃ Fin 4 := Fintype.equivOfCardEq (by simp)

private def nextFin : Equiv.Perm (Fin 4) :=
  ⟨fun x => x+1,fun x => x-1,by decide,by decide⟩

/-- Four private occurrences: none is the unary-pinned clone and the
other three belong to the original cubic graph legs. -/
def cycle : Equiv.Perm Index := (indexChart.trans nextFin).trans indexChart.symm

def Port {Pair G : Type*} : OrdinaryColumn Pair (OldNonPrivate Pair G) → Type
  | .inl _ => Bool
  | .inr (.inl _) => Bool
  | .inr (.inr _) => Option Bool

variable {Pair G : Type*}
variable (ends : G × Bool ≃ Pin Pair × Fin 3) (next : Equiv.Perm Index)

def route : OrdinaryWire Pair G → Sigma (Port (Pair:=Pair) (G:=G))
  | ((c,k),false) => ⟨.inr (.inl c),k⟩
  | ((.inl g,k),true) => ⟨.inr (.inr (ends (g,k))),none⟩
  | ((.inr (p,i),k),true) =>
    match if k then next i else i with
    | none => ⟨.inl p,k⟩
    | some j => ⟨.inr (.inr (p,j)),some k⟩

def routeBack : Sigma (Port (Pair:=Pair) (G:=G)) → OrdinaryWire Pair G
  | ⟨.inl p,k⟩ => ((.inr (p,if (show Bool from k) then next.symm none else none),k), true)
  | ⟨.inr (.inl c),k⟩ => ((c,k),false)
  | ⟨.inr (.inr v),none⟩ => ((.inl (ends.symm v).1,(ends.symm v).2),true)
  | ⟨.inr (.inr (p,j)),some k⟩ =>
    ((.inr (p,if k then next.symm (some j) else some j),k),true)

theorem route_leftInverse : Function.LeftInverse (routeBack ends next) (route ends next) := by
  rintro ⟨⟨g | ⟨p,i⟩,k⟩,b⟩ <;> cases b
  · rfl
  · simp [route,routeBack]
  · rfl
  · cases k with
    | false => cases i <;> simp [route,routeBack]
    | true =>
      cases h : next i with
      | none =>
        have hh : next.symm none = i := by rw [← h,Equiv.symm_apply_apply]
        simp [route,routeBack,h,hh]
      | some j =>
        have hh : next.symm (some j) = i := by rw [← h,Equiv.symm_apply_apply]
        simp [route,routeBack,h,hh]

def column (w : OrdinaryWire Pair G) : OrdinaryColumn Pair (OldNonPrivate Pair G) :=
  (route ends next w).1

private def fiberMap (c : OrdinaryColumn Pair (OldNonPrivate Pair G))
    (w : {w : OrdinaryWire Pair G // column ends next w = c}) : Port c :=
  w.prop ▸ (route ends next w.val).2

private theorem fiberMap_injective (c : OrdinaryColumn Pair (OldNonPrivate Pair G)) :
    Function.Injective (fiberMap ends next c) := by
  intro x y h
  apply Subtype.ext
  apply (route_leftInverse ends next).injective
  have hx : (⟨c,fiberMap ends next c x⟩ : Sigma Port) = route ends next x.val := by
    rcases x with ⟨x,hx⟩
    unfold column at hx
    subst c
    rfl
  have hy : (⟨c,fiberMap ends next c y⟩ : Sigma Port) = route ends next y.val := by
    rcases y with ⟨y,hy⟩
    unfold column at hy
    subst c
    rfl
  exact hx.symm.trans ((congrArg (Sigma.mk c) h).trans hy)

variable [Fintype Pair] [Fintype G]

include ends in
theorem actual_incidence :
    let N := Fintype.card (Pin Pair)
    Fintype.card (Wire Pair (OrdinaryWire Pair G)) = 24*N ∧ N%2=0 := by
  have hg := Fintype.card_congr ends
  simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at hg
  simp only [Wire, OrdinaryWire, OrdinaryRow, Binary, Index, Pin, Fintype.card_sum,
    Fintype.card_prod,Fintype.card_bool,Fintype.card_option,Fintype.card_fin] at hg ⊢
  omega

theorem clone_degree (p : Pin Pair) :
    (Finset.univ.filter fun w : OrdinaryWire Pair G => column ends next w = Sum.inl p).card ≤ 2 := by
  classical
  rw [← Fintype.card_subtype,← Nat.card_eq_fintype_card]
  letI : Finite (Port (G:=G) (Sum.inl p)) := inferInstanceAs (Finite Bool)
  have h := Nat.card_le_card_of_injective _ (fiberMap_injective ends next (Sum.inl p))
  change _ ≤ Nat.card Bool at h
  simpa only [Nat.card_eq_fintype_card (α:=Bool), Fintype.card_bool] using h

theorem ordinary_degree (c : OldNonPrivate Pair G) :
    (Finset.univ.filter fun w : OrdinaryWire Pair G => column ends next w = Sum.inr c).card ≤ 3 := by
  classical
  rw [← Fintype.card_subtype,← Nat.card_eq_fintype_card]
  cases c with
  | inl b =>
    letI : Finite (Port (Pair:=Pair) (G:=G) (Sum.inr (Sum.inl b))) := inferInstanceAs (Finite Bool)
    have h := Nat.card_le_card_of_injective _ (fiberMap_injective ends next (Sum.inr (Sum.inl b)))
    change _ ≤ Nat.card Bool at h
    exact (h.trans_eq (by rw [Nat.card_eq_fintype_card,Fintype.card_bool])).trans (by decide)
  | inr p =>
    letI : Finite (Port (Pair:=Pair) (G:=G) (Sum.inr (Sum.inr p))) := inferInstanceAs (Finite (Option Bool))
    have h := Nat.card_le_card_of_injective _ (fiberMap_injective ends next (Sum.inr (Sum.inr p)))
    change _ ≤ Nat.card (Option Bool) at h
    exact h.trans_eq (by rw [Nat.card_eq_fintype_card,Fintype.card_option,Fintype.card_bool])

#print axioms route_leftInverse
#print axioms actual_incidence
#print axioms clone_degree
#print axioms ordinary_degree

end
end J7PrintedParamsGraph
