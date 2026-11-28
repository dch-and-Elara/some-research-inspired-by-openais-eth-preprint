import J6R10ReachableTree
import J6R16ModeCostGeometric

/-! A proof-side occurrence ledger. Two different actual addresses
that reach the same Call are counted twice. This is not the deduped
set allSites, and the list is not working memory of the algorithm. -/
namespace J6R16ModeCost
open scoped BigOperators Classical
open J6R10Reachable

theorem reach_snoc {X : Type*} (P : FinitePlan X) {r x : X}
    (h : NativeReach P r x) (w : P.Slot x) :
    NativeReach P r (P.child x w) := by
  induction h with
  | reflexive => exact .step w (.reflexive _)
  | step v _ ih => exact .step v (ih w)

noncomputable def slotOrder {X : Type*} (P : FinitePlan X) (c : X) : List (P.Slot c) := by
  letI : Fintype (P.Slot c) := P.finiteSlot c
  exact (Finset.univ : Finset (P.Slot c)).toList

theorem slotOrder_len {X : Type*} (P : FinitePlan X) (c : X) :
    (slotOrder P c).length=Nat.card (P.Slot c) := by
  letI : Fintype (P.Slot c) := P.finiteSlot c
  rw [slotOrder,Finset.length_toList,Finset.card_univ,Nat.card_eq_fintype_card]

noncomputable def childList {X : Type*} (P : FinitePlan X) (c : X) : List X :=
  (slotOrder P c).map (P.child c)

theorem childList_len {X : Type*} (P : FinitePlan X) (c : X) :
    (childList P c).length=Nat.card (P.Slot c) := by
  rw [childList,List.length_map,slotOrder_len]

noncomputable def occurrences {X : Type*} (P : FinitePlan X) (r : X) : ℕ→List X
  | 0 => [r]
  | d+1 => (occurrences P r d).flatMap (childList P)

theorem occurrence_reach_depth {X : Type*} (P : FinitePlan X) (depth : X→ℕ)
    (next : ∀ c (w : P.Slot c),depth (P.child c w)=depth c+1)
    (r : X) (d : ℕ) (c : X) (h : c∈occurrences P r d) :
    NativeReach P r c ∧ depth c=depth r+d := by
  induction d generalizing c with
  | zero =>
    simp only [occurrences,List.mem_singleton] at h
    subst c
    exact ⟨.reflexive _,by simp⟩
  | succ d ih =>
    rw [occurrences,List.mem_flatMap] at h
    obtain ⟨x,hx,hc⟩ := h
    obtain ⟨hxR,hxD⟩ := ih x hx
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hc
    exact ⟨reach_snoc P hxR w,by rw [next,hxD]; rfl⟩

theorem list_sum_cap {X : Type*} (ss : List X) (f : X→ℕ) (B : ℕ)
    (h : ∀ x∈ss,f x≤B) :
    (ss.map f).sum≤ss.length*B := by
  induction ss with
  | nil => simp
  | cons x xs ih =>
    have ht := ih (fun y hy=>h y (List.mem_cons_of_mem _ hy))
    have hx := h x List.mem_cons_self
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    omega

theorem occurrences_product {X : Type*} (P : FinitePlan X) (r : X) (B : ℕ→ℕ)
    (hLocal : ∀ d c,c∈occurrences P r d → Nat.card (P.Slot c)≤B d) (d : ℕ) :
    (occurrences P r d).length≤∏ j∈Finset.range d,B j := by
  induction d with
  | zero => simp [occurrences]
  | succ d ih =>
    rw [occurrences,List.length_flatMap,Finset.prod_range_succ]
    have h := list_sum_cap (occurrences P r d) (fun c=>(childList P c).length) (B d)
      (fun c hc=> (childList_len P c).trans_le (hLocal d c hc))
    exact h.trans (Nat.mul_le_mul_right _ ih)

theorem occurrences_envelope {X : Type*} (P : FinitePlan X) (r : X)
    (s C lam K b : ℕ)
    (h : ∀ d c,c∈occurrences P r d →
      Nat.card (P.Slot c)≤2^(b+depthExponent s C lam K d)) (d : ℕ) :
    (occurrences P r d).length≤2^(b*d+24*depthScale s C lam K) :=
  (occurrences_product P r _ h d).trans (depth_product s C lam K b d)

theorem total_occur_bound {X : Type*} (P : FinitePlan X) (r : X)
    (s C lam K b H : ℕ)
    (h : ∀ d c,c∈occurrences P r d →
      Nat.card (P.Slot c)≤2^(b+depthExponent s C lam K d)) :
    (∑ d∈Finset.range (H+1),(occurrences P r d).length)≤
      (H+1)*2^(b*H+24*depthScale s C lam K) := by
  calc
    _≤∑ d∈Finset.range (H+1), (2:ℕ)^(b*H+24*depthScale s C lam K) := by
      apply Finset.sum_le_sum
      intro d hd
      apply (occurrences_envelope P r s C lam K b h d).trans
      apply Nat.pow_le_pow_right (by decide)
      exact Nat.add_le_add_right (Nat.mul_le_mul_left b
        (Nat.le_of_lt_succ (Finset.mem_range.mp hd))) _
    _=_ := by simp

theorem total_fee_bound {X : Type*} (P : FinitePlan X) (r : X)
    (s C lam K b H G : ℕ) (fee : X→ℕ)
    (h : ∀ d c,c∈occurrences P r d →
      Nat.card (P.Slot c)≤2^(b+depthExponent s C lam K d))
    (hFee : ∀ d c,c∈occurrences P r d →
      fee c≤G*2^(b+depthExponent s C lam K d)) :
    (∑ d∈Finset.range H, ((occurrences P r d).map fee).sum)≤
      H*G*2^(b*H+24*depthScale s C lam K) := by
  calc
    _≤∑ _∈Finset.range H, G*2^(b*H+24*depthScale s C lam K) := by
      apply Finset.sum_le_sum
      intro d hd
      let B := fun j=>(2:ℕ)^(b+depthExponent s C lam K j)
      have P_d := occurrences_product P r B h d
      calc
        _≤(occurrences P r d).length*(G*B d) :=
          list_sum_cap _ _ _ (fun c hc=>hFee d c hc)
        _≤(∏ j∈Finset.range d,B j)*(G*B d) := Nat.mul_le_mul_right _ P_d
        _=G*(∏ j∈Finset.range (d+1),B j) := by rw [Finset.prod_range_succ]; ring
        _≤G*2^(b*(d+1)+24*depthScale s C lam K) :=
          Nat.mul_le_mul_left G (depth_product s C lam K b _)
        _≤_ := by
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_right (by decide)
          exact Nat.add_le_add_right (Nat.mul_le_mul_left b (Finset.mem_range.mp hd)) _
    _=_ := by simp [Nat.mul_assoc]

#print axioms occurrence_reach_depth
#print axioms occurrences_product
#print axioms total_occur_bound
#print axioms total_fee_bound
end J6R16ModeCost


