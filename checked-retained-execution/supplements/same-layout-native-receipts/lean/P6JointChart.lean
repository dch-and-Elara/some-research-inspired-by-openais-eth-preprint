import P9SeatPhysical

namespace Paper6JointSeating
open P11FullPacking P9BalancedChart

variable {W K : Type*} [Fintype W] [LinearOrder K] [Fintype K] {a b : ℕ}

theorem place_exhausted_endpoints (ha : 0 < a)
    (label : W → Cell (Fin a) K) (mark : W → Option Bool)
    (cap : ∀ c, Nat.card (RealFiber label c) ≤ b*2^a)
    (exactCap : ∀ c s, Nat.card (Marked label mark c s) = b) :
    ∃ j : W ↪ Physical a b K,
      (∀ w, physicalCell (balancedMask a b K) (j w) = label w) ∧
      (∀ w s, (j w).2 = endpointIndex a s ↔ mark w = some s) ∧
      (∀ z s, z.2 = endpointIndex a s → ∃ w, j w = z) := by
  classical
  obtain ⟨j,hj,he⟩ := place_all ha label mark cap (fun c s => (exactCap c s).le)
  let e (c : Cell (Fin a) K) (s : Bool) :
      Marked label mark c s ↪ ActualEnd a b c s :=
    ⟨fun w => ⟨j w.val.val, (hj _).trans w.val.prop, he _ _ w.prop⟩,
      fun x y h => Subtype.ext (Subtype.ext (j.injective (congrArg Subtype.val h)))⟩
  have surj (c : Cell (Fin a) K) (s : Bool) : Function.Surjective (e c s) := by
    have hs : Fintype.card (Marked label mark c s) = Fintype.card (ActualEnd a b c s) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, actual_end_card, exactCap]
    exact (Fintype.bijective_iff_injective_and_card _).mpr ⟨(e c s).injective,hs⟩ |>.2
  have exhaust (z : Physical a b K) (s : Bool) (hz : z.2 = endpointIndex a s) :
      ∃ w, j w = z ∧ mark w = some s := by
    obtain ⟨w,hw⟩ := surj (physicalCell (balancedMask a b K) z) s ⟨z,rfl,hz⟩
    exact ⟨w.val.val,congrArg Subtype.val hw,w.prop⟩
  refine ⟨j,hj,fun w s => ⟨?_, he w s⟩,?_⟩
  · intro h
    obtain ⟨v,hv,hs⟩ := exhaust (j w) s h
    rwa [j.injective hv] at hs
  · intro z s h
    obtain ⟨w,hw,_⟩ := exhaust z s h
    exact ⟨w,hw⟩

#print axioms place_exhausted_endpoints
end Paper6JointSeating
