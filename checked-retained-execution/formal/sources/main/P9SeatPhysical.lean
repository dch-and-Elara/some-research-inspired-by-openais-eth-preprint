import P9BalancedChart

/-! Fill the non-guarded real ports and padding without undoing any
prescribed guarded endpoint. The endpoint targets are actual slot indices. -/

namespace P9BalancedChart
open P11FullPacking

theorem extend_partial {A B : Type*} [Fintype A] [Fintype B] (p : A → Prop)
    [DecidablePred p] (h : Fintype.card A ≤ Fintype.card B) (e : {x // p x} ↪ B) :
    ∃ f : A ↪ B, ∀ x (hx : p x), f x = e ⟨x,hx⟩ := by
  classical
  let q : B → Prop := fun y => y ∈ Set.range e
  have hq : Fintype.card {y // q y} = Fintype.card {x // p x} := by
    exact (Fintype.card_congr (Equiv.ofInjective (fun x => e x) e.injective)).symm
  have hc : Fintype.card {x // ¬ p x} ≤ Fintype.card {y // ¬ q y} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hq]
    exact Nat.sub_le_sub_right h _
  obtain ⟨g⟩ := Function.Embedding.nonempty_of_card_le hc
  let f (x : A) : B := if hx : p x then e ⟨x,hx⟩ else (g ⟨x,hx⟩).val
  have hf : Function.Injective f := by
    intro x y hh
    by_cases hx : p x <;> by_cases hy : p y
    · have eh : e ⟨x,hx⟩ = e ⟨y,hy⟩ := by
        simpa only [f, dif_pos hx, dif_pos hy] using hh
      exact congrArg Subtype.val (e.injective eh)
    · have eh : e ⟨x,hx⟩ = (g ⟨y,hy⟩).val := by simpa [f,hx,hy] using hh
      exact False.elim ((g ⟨y,hy⟩).prop ⟨⟨x,hx⟩,eh⟩)
    · have eh : (g ⟨x,hx⟩).val = e ⟨y,hy⟩ := by simpa [f,hx,hy] using hh
      exact False.elim ((g ⟨x,hx⟩).prop ⟨⟨y,hy⟩,eh.symm⟩)
    · have e' : (g ⟨x,hx⟩).val = (g ⟨y,hy⟩).val := by simpa [f,hx,hy] using hh
      exact congrArg Subtype.val (g.injective (Subtype.ext e'))
  exact ⟨⟨f,hf⟩, fun x hx => dif_pos hx⟩

variable {K : Type*} [LinearOrder K] [Fintype K] {W : Type*} [Fintype W] {a b : ℕ}

abbrev Marked (label : W → Cell (Fin a) K) (mark : W → Option Bool)
    (c : Cell (Fin a) K) (right : Bool) :=
  {w : RealFiber label c // mark w = some right}

abbrev FullCell (a b : ℕ) {K : Type*} [LinearOrder K] (c : Cell (Fin a) K) :=
  {z : Physical a b K // physicalCell (balancedMask a b K) z = c}

noncomputable def fullCellEquiv (c : Cell (Fin a) K) :
    FullCell a b c ≃ Fin (b*2^a) where
  toFun z := (fullSlotChart (balancedMask a b K) z.val).2
  invFun j := ⟨(fullSlotChart (balancedMask a b K)).symm (c,j), by
    rw [← fullSlotChart_cell, Equiv.apply_symm_apply]⟩
  left_inv := by
    intro z
    apply Subtype.ext
    apply (fullSlotChart (balancedMask a b K)).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext (z.prop.symm.trans (fullSlotChart_cell _ _).symm) rfl
  right_inv := by intro j; simp

/-- All real wires are placed in their original label cells. Marked
wires are simultaneously at the prescribed actual endpoint. -/
theorem place_all (ha : 0 < a) (label : W → Cell (Fin a) K) (mark : W → Option Bool)
    (cap : ∀ c, Nat.card (RealFiber label c) ≤ b*2^a)
    (markedCap : ∀ c s, Nat.card (Marked label mark c s) ≤ b) :
    ∃ seat : W ↪ Physical a b K,
      (∀ w, physicalCell (balancedMask a b K) (seat w) = label w) ∧
      ∀ w s, mark w = some s → (seat w).2 = endpointIndex a s := by
  classical
  have byCell (c : Cell (Fin a) K) :
      ∃ f : RealFiber label c ↪ FullCell a b c,
        ∀ (w : RealFiber label c) s, mark w.val = some s → (f w).val.2 = endpointIndex a s := by
    have hpart (s : Bool) : Nonempty (Marked label mark c s ↪ ActualEnd a b c s) := by
      apply Function.Embedding.nonempty_of_card_le
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, actual_end_card]
      exact markedCap c s
    let choices := fun s => Classical.choice (hpart s)
    let p (w : RealFiber label c) : Prop := ∃ s, mark w = some s
    let pick (s : Bool) (w : RealFiber label c) (h : mark w = some s) : FullCell a b c :=
      ⟨(choices s ⟨w,h⟩).val,(choices s ⟨w,h⟩).prop.1⟩
    let e (w : {x // p x}) : FullCell a b c :=
      if h : mark w.val = some false then pick false w.val h
      else pick true w.val (by
        obtain ⟨s,hs⟩ := w.prop
        cases s
        · exact False.elim (h hs)
        · exact hs)
    have hpick (w : {x // p x}) (s : Bool) (hw : mark w.val = some s) :
        e w = pick s w.val hw := by
      cases s
      · simp [e,hw]
      · have h : mark w.val ≠ some false := by simp [hw]
        simp [e,h]
    have hs (w : {x // p x}) (s : Bool) (hw : mark w.val = some s) :
        (e w).val.2 = endpointIndex a s := by
      rw [hpick w s hw]
      exact (choices s ⟨w.val,hw⟩).prop.2
    have eInj : Function.Injective e := by
      intro w w' eq
      have hp (s t : Bool) (h : endpointIndex a s = endpointIndex a t) : s=t := by
        cases s <;> cases t
        · rfl
        · exact False.elim (different_ends ha h)
        · exact False.elim (different_ends ha h.symm)
        · rfl
      obtain ⟨s,h0⟩ := w.prop
      obtain ⟨t,h1⟩ := w'.prop
      have ht : s=t := hp s t ((hs w s h0).symm.trans
        ((congrArg (fun u : FullCell a b c => u.val.2) eq).trans (hs w' t h1)))
      subst t
      rw [hpick w s h0, hpick w' s h1] at eq
      have he : (choices s ⟨w.val,h0⟩).val = (choices s ⟨w'.val,h1⟩).val :=
        congrArg (fun z : FullCell a b c => z.val) eq
      exact Subtype.ext (congrArg (fun y : Marked label mark c s => y.val)
        ((choices s).injective (Subtype.ext he)))
    have hf : Fintype.card (RealFiber label c) ≤ Fintype.card (FullCell a b c) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        Nat.card_congr (fullCellEquiv (b:=b) c), Nat.card_fin]
      exact cap c
    obtain ⟨f,hf⟩ := extend_partial p hf ⟨e,eInj⟩
    refine ⟨f,?_⟩
    intro w s hw
    have hwp : p w := ⟨s,hw⟩
    rw [hf w hwp]
    exact hs ⟨w,hwp⟩ s hw
  choose g hg using byCell
  let gSigma : (Σ c, RealFiber label c) ↪ (Σ c, FullCell a b c) :=
    Function.Embedding.sigmaMap (Function.Embedding.refl _) g
  let final := (Equiv.sigmaFiberEquiv label).symm.toEmbedding.trans
    (gSigma.trans (Equiv.sigmaFiberEquiv (physicalCell (balancedMask a b K))).toEmbedding)
  refine ⟨final,?_,?_⟩
  · intro w
    exact (g (label w) ⟨w,rfl⟩).prop
  · intro w s hw
    exact hg _ ⟨w,rfl⟩ s hw

#print axioms extend_partial
#print axioms fullCellEquiv
#print axioms place_all

end P9BalancedChart