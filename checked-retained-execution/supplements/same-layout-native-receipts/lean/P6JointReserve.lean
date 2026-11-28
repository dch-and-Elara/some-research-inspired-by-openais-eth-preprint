import P6JointFill
import P6JointChart

namespace Paper6JointSeating
open P11FullPacking P9BalancedChart

theorem reserveAndPlace {W K R : Type*} [Fintype W] [DecidableEq W]
    [LinearOrder K] [Fintype K] {a b : ℕ} (ha : 0<a)
    (label : W → Cell (Fin a) K) (row : W → R) (nonpin : W → Prop)
    (r0 r1 pool0 pool1 : Cell (Fin a) K → Finset W)
    (cap : ∀ c, Nat.card (RealFiber label c) ≤ b*2^a)
    (sizeR0 : ∀ c, (r0 c).card ≤ b) (sizeR1 : ∀ c, (r1 c).card ≤ b)
    (size0 : ∀ c, b - (r0 c).card ≤ (pool0 c).card)
    (size1 : ∀ c, 2*b ≤ (pool1 c).card)
    (labels : ∀ c w, w ∈ r0 c ∨ w ∈ r1 c ∨ w ∈ pool0 c ∨ w ∈ pool1 c →
        label w = c ∧ nonpin w)
    (rd : ∀ c, Disjoint (r0 c) (r1 c))
    (avoid0 : ∀ c, Disjoint (r0 c) (pool0 c))
    (avoid1 : ∀ c, Disjoint (r1 c) (pool0 c))
    (rowR : Set.InjOn row {w | w ∈ r0 (label w)})
    (rowP : Set.InjOn row {w | w ∈ pool0 (label w)})
    (rowApart : ∀ x y, x ∈ r0 (label x) → y ∈ pool0 (label y) → row x ≠ row y) :
    ∃ seat : W ↪ Physical a b K,
      (∀ w, physicalCell (balancedMask a b K) (seat w) = label w) ∧
      (∀ w, w ∈ r0 (label w) → (seat w).2 = endpointIndex a false) ∧
      (∀ w, w ∈ r1 (label w) → (seat w).2 = endpointIndex a true) ∧
      (∀ z s, z.2 = endpointIndex a s → ∃ w, seat w = z) ∧
      (∀ w s, (seat w).2 = endpointIndex a s → nonpin w) ∧
      Set.InjOn row {w | (seat w).2 = endpointIndex a false} := by
  classical
  obtain ⟨s0,s1,hs,hlab,hrow⟩ := fillEndpointSets label row nonpin r0 r1 pool0 pool1 b sizeR0
    sizeR1 size0 size1 labels rd avoid0 avoid1 rowR rowP rowApart
  let pick (s : Bool) := if s then s1 else s0
  let mark (w : W) : Option Bool :=
    if w ∈ s0 (label w) then some false else if w ∈ s1 (label w) then some true else none
  have iffM (w : W) (s : Bool) : mark w = some s ↔ w ∈ pick s (label w) := by
    cases s
    · simp [mark,pick]
    · by_cases hh : w ∈ s0 (label w)
      · have no := Finset.disjoint_left.mp (hs (label w)).2.2.1 hh
        simp [mark,pick,hh,no]
      · simp [mark,pick,hh]
  have cardM (c : Cell (Fin a) K) (s : Bool) : Nat.card (Marked label mark c s) = b := by
    have pin (w : W) (h : w ∈ pick s c) : label w = c := by
      cases s
      · exact (hlab c w (Or.inl h)).1
      · exact (hlab c w (Or.inr h)).1
    let e : Marked label mark c s ≃ {w // w ∈ pick s c} :=
      { toFun := fun w => ⟨w.val.val,by
          simpa only [w.val.prop] using (iffM w.val.val s).mp w.prop⟩
        invFun := fun w => ⟨⟨w.val,pin w.val w.prop⟩,(iffM w.val s).mpr (by
          simpa only [pin w.val w.prop] using w.prop)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    cases s
    · exact (hs c).2.2.2.1
    · exact (hs c).2.2.2.2
  obtain ⟨seat,hp,hiff,hex⟩ := place_exhausted_endpoints ha label mark cap cardM
  refine ⟨seat,hp,?_,?_,hex,?_,?_⟩
  · intro w hw
    exact (hiff w false).mpr ((iffM w false).mpr ((hs (label w)).1 hw))
  · intro w hw
    exact (hiff w true).mpr ((iffM w true).mpr ((hs (label w)).2.1 hw))
  · intro w s hw
    have hm := (iffM w s).mp ((hiff w s).mp hw)
    cases s
    · exact (hlab _ w (Or.inl hm)).2
    · exact (hlab _ w (Or.inr hm)).2
  · intro x hx y hy
    exact hrow ((iffM x false).mp ((hiff x false).mp hx))
      ((iffM y false).mp ((hiff y false).mp hy))

#print axioms reserveAndPlace
end Paper6JointSeating
