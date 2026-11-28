import P9SeatPhysical

namespace P9BalancedChart
open scoped BigOperators
open GuardExpectation GuardedPacking P11FullPacking OuterNodePacking

section Marking

variable {E C : Type*} [Fintype E] [DecidableEq E] [Fintype C] [DecidableEq C]

omit [Fintype E] [DecidableEq E] [Fintype C] in
theorem multiplicity_eq (label : E → Bool → C) (e : E) (c : C) :
    portMultiplicity label e c = multiplicity label e c := by
  simp [portMultiplicity, GuardedPacking.multiplicity, Fintype.card_subtype]

/-- Whole-vertex marking with the paper's loss terms on the actual
ordered-cell alphabet. This form does not assume cell labels are bits. -/
theorem select_capacity {L : ℕ} (hL : 2 ≤ L)
    (label : E → Bool → C) (b : ℕ)
    (capacity : ∀ c, ((cellLoad (multiplicity label) Finset.univ c : ℕ) : ℝ) / L ≤ b) :
    ∃ keep : Bool → Finset E,
      Disjoint (keep false) (keep true) ∧
      ∀ s : Bool, (∀ c, cellLoad (multiplicity label) (keep s) c ≤ b) ∧
        (Fintype.card E : ℝ) / L ≤ (keep s).card +
          Real.sqrt (5 * (2 * (Fintype.card E : ℝ)) / L) +
          Real.sqrt ((Fintype.card C : ℝ) * (5 * (2 * (Fintype.card E : ℝ)) / L)) := by
  classical
  obtain ⟨a, ha, hpot⟩ := exists_port_marking_by_conditioning hL label
  let m := fun s => markedSet a (signSymbol L hL s)
  let μ := fun c => ((cellLoad (multiplicity label) Finset.univ c : ℕ) : ℝ) / L
  let B : ℝ := 5 * (2 * (Fintype.card E : ℝ)) / L
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have one (s : Bool) :
      ((m s).card - (Fintype.card E : ℝ)/L)^2 +
        (∑ c, ((cellLoad (multiplicity label) (m s) c : ℝ) - μ c)^2) ≤ B := by
    let v := fun t : Bool =>
      (centeredLoad (L : ℚ)⁻¹ (signSymbol L hL t) (fun _ => 1) a)^2 +
        ∑ c, (centeredLoad (L : ℚ)⁻¹ (signSymbol L hL t)
          (fun e => (portMultiplicity label e c : ℚ)) a)^2
    have hv : v s ≤ ∑ t, v t :=
      Finset.single_le_sum (fun t _ => by dsimp [v]; positivity) (Finset.mem_univ s)
    have hr := hv.trans hpot
    have hc0 : centeredLoad (L : ℚ)⁻¹ (signSymbol L hL s) (fun _ => 1) a =
        ((m s).card : ℚ) - (Fintype.card E : ℚ)/L := by
      simpa [m, div_eq_mul_inv] using
        (GuardAssembly.centered_marked a (signSymbol L hL s) (fun (_ : E) => 1))
    have hc1 (c : C) :
        centeredLoad (L : ℚ)⁻¹ (signSymbol L hL s)
          (fun e => (portMultiplicity label e c : ℚ)) a =
        (cellLoad (multiplicity label) (m s) c : ℚ) -
          (cellLoad (multiplicity label) Finset.univ c : ℚ)/L := by
      simpa [m, cellLoad, div_eq_mul_inv, multiplicity_eq, Nat.cast_sum] using
        (GuardAssembly.centered_marked a (signSymbol L hL s) (fun e => portMultiplicity label e c))
    change (centeredLoad _ _ _ a)^2 + ∑ c, (centeredLoad _ _ _ a)^2 ≤ _ at hr
    simp only [hc0, hc1] at hr
    dsimp [μ, B]
    have hr' := (Rat.cast_le (K := ℝ)).mpr hr
    push_cast at hr'
    exact hr'
  have build (s : Bool) : ∃ t : Finset E, t ⊆ m s ∧
      (∀ c : C, cellLoad (multiplicity label) t c ≤ b) ∧
      (Fintype.card E : ℝ) / L ≤ t.card + Real.sqrt B +
        Real.sqrt ((Fintype.card C : ℝ) * B) := by
    have h := one s
    have hs : ((m s).card - (Fintype.card E : ℝ)/L)^2 ≤ B :=
      (le_add_of_nonneg_right (by positivity)).trans h
    have hd : (∑ c, ((cellLoad (multiplicity label) (m s) c : ℝ) - μ c)^2) ≤ B :=
      (le_add_of_nonneg_left (sq_nonneg _)).trans h
    have ht : (Fintype.card E : ℝ)/L - (m s).card ≤ Real.sqrt B := by
      by_cases hneg : (Fintype.card E : ℝ)/L - (m s).card ≤ 0
      · exact hneg.trans (Real.sqrt_nonneg _)
      · apply (Real.le_sqrt (le_of_not_ge hneg) hB).mpr
        nlinarith

    obtain ⟨t, hts, htc, htb⟩ := retain_from_deviations
      (multiplicity label) (fun _ => b) (m s) μ capacity B hB hd
    exact ⟨t, hts, htc, by linarith⟩
  choose keep hsub hseat hret using build
  exact ⟨keep, Finset.disjoint_left.mpr (fun e he hf =>
    Finset.disjoint_left.mp ha (hsub false he) (hsub true hf)),
    fun s => ⟨hseat s, hret s⟩⟩

end Marking

section Physical

variable {K E : Type*} [LinearOrder K] [Fintype K]
  [Fintype E] [DecidableEq E] [Nonempty E] {a b : ℕ} [DecidableEq (Page a b K)]

def signedMark (keep : Bool → Finset E) (w : E×Bool) : Option Bool :=
  if w.1 ∈ keep false then some false else if w.1 ∈ keep true then some true else none

omit [Fintype E] [Nonempty E] in
theorem marked_iff (keep : Bool → Finset E) (h : Disjoint (keep false) (keep true))
    (w : E×Bool) (s : Bool) : signedMark keep w = some s ↔ w.1 ∈ keep s := by
  cases s
  · by_cases e : w.1 ∈ keep false <;> simp [signedMark,e]
  · by_cases e : w.1 ∈ keep false
    · have h' : w.1 ∉ keep true := fun h₀ => Finset.disjoint_left.mp h e h₀
      simp [signedMark,e,h']
    · simp [signedMark,e]

def wholeFiberEquiv (label : E → Bool → Cell (Fin a) K) (c : Cell (Fin a) K) :
    RealFiber (fun w : E × Bool => label w.1 w.2) c ≃ markedPort label Finset.univ c where
  toFun w := ⟨⟨w.val.1,Finset.mem_univ _⟩,⟨w.val.2,w.prop⟩⟩
  invFun w := ⟨(w.1.val,w.2.val),w.2.prop⟩
  left_inv w := by cases w; rfl
  right_inv w := by cases w; rfl

def markedFiberEquiv (label : E → Bool → Cell (Fin a) K) (c : Cell (Fin a) K)
    (keep : Bool → Finset E) (hh : Disjoint (keep false) (keep true)) (s : Bool) :
    Marked (fun w : E×Bool => label w.1 w.2) (signedMark keep) c s ≃ markedPort label (keep s) c where
  toFun w := ⟨⟨w.val.val.1,(marked_iff keep hh _ s).mp w.prop⟩,⟨w.val.val.2,w.val.prop⟩⟩
  invFun w := ⟨⟨(w.1.val,w.2.val),w.2.prop⟩,(marked_iff keep hh _ s).mpr w.1.prop⟩
  left_inv w := by cases w; rfl
  right_inv w := by cases w; rfl

/-- P9 on the actual dyadic slot chart. Every real wire gets a distinct
seat in its original ordered cell, and the same seating simultaneously
protects all nonzero shifts. The theorem is finite and needs no
asymptotic or algorithmic existence hypothesis beyond the input loads. -/
theorem guarded_real_layout (ha : 0 < a)
    (label : E → Bool → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber (fun w : E × Bool => label w.1 w.2) c) ≤ b*2^a) :
    ∃ seat : E×Bool ↪ Physical a b K,
      (∀ w, physicalCell (balancedMask a b K) (seat w) = label w.1 w.2) ∧
      ∀ (packets : Finset (Page a b K)) (t : ℤ), t ≠ 0 →
        (Fintype.card E : ℝ)/(2^a : ℕ) ≤
        ((untouched Finset.univ (vertexOwner seat)
          (matchedColumns packets (realSlot seat) (realSlot seat) t)).card : ℝ) +
        Real.sqrt (5*(2*(Fintype.card E : ℝ))/(2^a : ℕ)) +
        Real.sqrt ((Fintype.card (Cell (Fin a) K) : ℝ) *
          (5*(2*(Fintype.card E : ℝ))/(2^a : ℕ))) := by
  classical
  have hL : 2 ≤ 2^a := (pow_one 2).symm.trans_le (Nat.pow_le_pow_right (by decide) ha)
  have hc (c : Cell (Fin a) K) :
      ((cellLoad (multiplicity label) Finset.univ c : ℕ) : ℝ) / (2^a:ℕ) ≤ b := by
    apply (div_le_iff₀ (by positivity)).2
    have hh := cap c
    rw [Nat.card_congr (wholeFiberEquiv label c), Nat.card_eq_fintype_card, card_markedPort] at hh
    exact_mod_cast hh
  obtain ⟨keep,hd,hkeep⟩ := select_capacity hL label b hc
  have hm (c : Cell (Fin a) K) (s : Bool) :
      Nat.card (Marked (fun w : E×Bool => label w.1 w.2) (signedMark keep) c s) ≤ b := by
    rw [Nat.card_congr (markedFiberEquiv label c keep hd s),
      Nat.card_eq_fintype_card, card_markedPort]
    exact (hkeep s).1 c
  obtain ⟨seat,hs,he⟩ := place_all ha (fun w : E×Bool => label w.1 w.2)
    (signedMark keep) cap hm
  refine ⟨seat,hs,?_⟩
  intro packets t ht
  have hside (s : Bool) : (keep s).card ≤
      (P11SourceGeometry.seated Finset.univ (fun e p => seat (e,p)) s).card := by
    apply Finset.card_le_card
    intro e he'
    apply (P11SourceGeometry.mem_seated _ _ _ _).mpr
    refine ⟨Finset.mem_univ _,fun p => ?_⟩
    exact congrArg Fin.val (he (e,p) s ((marked_iff keep hd (e,p) s).mpr he'))
  have hAll := P11SourceGeometry.both_endpoint_counts_le_every_shift
    (Finset.univ : Finset E) packets (fun e p => seat (e,p))
    (realSlot seat) (realSlot seat) (vertexOwner seat) (real_fullPortFiber seat) t ht
  have h := (min_le_min (hside false) (hside true)).trans hAll
  by_cases hh : (keep false).card ≤ (keep true).card
  · rw [min_eq_left hh] at h
    have h' : ((keep false).card : ℝ) ≤
      ((untouched Finset.univ (vertexOwner seat)
        (matchedColumns packets (realSlot seat) (realSlot seat) t)).card : ℝ) := by exact_mod_cast h
    linarith [(hkeep false).2]
  · rw [min_eq_right (le_of_not_ge hh)] at h
    have h' : ((keep true).card : ℝ) ≤
      ((untouched Finset.univ (vertexOwner seat)
        (matchedColumns packets (realSlot seat) (realSlot seat) t)).card : ℝ) := by exact_mod_cast h
    linarith [(hkeep true).2]

end Physical

#print axioms guarded_real_layout
#print axioms select_capacity

end P9BalancedChart