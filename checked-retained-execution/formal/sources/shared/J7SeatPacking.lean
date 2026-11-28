import P11FullPackingPlacement

/-! # J7 balanced packet endpoints and constrained seating -/

open scoped BigOperators Classical

namespace J7SeatPacking
open P11FullPacking

noncomputable section
set_option maxHeartbeats 1200000

/-- Unlike P11's common-mask convention, J7 uses every orientation the
same number of times within each unordered packet type. -/
def balancedMask {K : Type*} [LinearOrder K] (a b : ℕ) : MaskFamily a b K :=
  fun _ p => p.2

abbrev Side {K : Type*} [LinearOrder K] (a b : ℕ)
    (c : Cell (Fin a) K) (right : Bool) :=
  {p : Page a b K // physicalCell (balancedMask a b) (p,endpointIndex a right) = c}

variable {K : Type*} [LinearOrder K] {a b : ℕ}

theorem cell_endpoint_decoded (c : Cell (Fin a) K) (right : Bool) (i : Fin b) :
    physicalCell (balancedMask a b)
      (⟨key c,(i,GuardedPacking.endMask right (orientation c))⟩,endpointIndex a right) = c := by
  unfold physicalCell
  change cell (key c)
      (slotOrient (key c) (GuardedPacking.endMask right (orientation c)) (endpointIndex a right)) = c
  rw [slotOrient_endpoint _ _ right _ rfl, GuardedPacking.endMask_involutive right, cell_decode]

/-- Exactly one orientation per copy gives a fixed ordered cell at either
specified endpoint, including cells with equal symbols. -/
def sideEquiv (c : Cell (Fin a) K) (right : Bool) : Side a b c right ≃ Fin b where
  toFun p := p.val.2.1
  invFun i := ⟨⟨key c,(i,GuardedPacking.endMask right (orientation c))⟩,cell_endpoint_decoded c right i⟩
  right_inv _ := rfl
  left_inv := by
    rintro ⟨⟨k,i,m⟩,hm⟩
    change cell k (slotOrient k m (endpointIndex a right)) = c at hm
    rw [slotOrient_endpoint _ _ right _ rfl] at hm
    have hk : k = key c := by
      have h := congrArg key hm
      rwa [key_cell] at h
    subst k
    have he : GuardedPacking.endMask right m = orientation c :=
      cell_injective (key c) (hm.trans (cell_decode c).symm)
    have hh : m = GuardedPacking.endMask right (orientation c) :=
      (GuardedPacking.endMask_involutive right m).symm.trans
        (congrArg (GuardedPacking.endMask right) he)
    subst m
    rfl

/-- The two physical endpoints themselves, before assigning real wires. -/
def isEnd (s : Physical a b K) : Prop := s.2.val = 0 ∨ s.2.val = 2^a-1

abbrev SlotFiber (c : Cell (Fin a) K) := {s : Physical a b K // physicalCell (balancedMask a b) s = c}
abbrev EndFiber (c : Cell (Fin a) K) := {s : SlotFiber (a:=a) (b:=b) c // isEnd s.val}

theorem side_index_ne (ha : 0 < a) :
    endpointIndex a false ≠ endpointIndex a true := by
  intro h
  exact GuardedPacking.endpoints_ne (L:=2^a)
    (by change (2:ℕ)^1 ≤ 2^a; exact Nat.pow_le_pow_right (by decide) ha)
    (congrArg Fin.val h)

/-- Disjoint left and right endpoint sets in each ordered cell. -/
def endsEquiv (ha : 0 < a) (c : Cell (Fin a) K) : (Side a b c false ⊕ Side a b c true) ≃ EndFiber (b:=b) c := by
  classical
  let left : Side a b c false → EndFiber (b:=b) c :=
    fun p => ⟨⟨(p.val,endpointIndex a false),p.prop⟩,Or.inl rfl⟩
  let right : Side a b c true → EndFiber (b:=b) c :=
    fun p => ⟨⟨(p.val,endpointIndex a true),p.prop⟩,Or.inr rfl⟩
  refine Equiv.ofBijective (Sum.elim left right) ⟨?_,?_⟩
  · rintro (p | p) (q | q) he
    · exact congrArg Sum.inl (Subtype.ext (congrArg (fun z : EndFiber (b:=b) c => z.val.val.1) he))
    · exact (side_index_ne ha (congrArg (fun z : EndFiber (b:=b) c => z.val.val.2) he)).elim
    · exact (side_index_ne ha (congrArg (fun z : EndFiber (b:=b) c => z.val.val.2) he).symm).elim
    · exact congrArg Sum.inr (Subtype.ext (congrArg (fun z : EndFiber (b:=b) c => z.val.val.1) he))
  · rintro ⟨⟨⟨p,x⟩,hp⟩,he⟩
    rcases he with h | h
    · have hx : x = endpointIndex a false := Fin.ext h
      subst x
      exact ⟨Sum.inl ⟨p,hp⟩,rfl⟩
    · have hx : x = endpointIndex a true := Fin.ext h
      subst x
      exact ⟨Sum.inr ⟨p,hp⟩,rfl⟩

theorem card_ends (ha : 0 < a) (c : Cell (Fin a) K) :
    Nat.card (EndFiber (b:=b) c) = 2*b := by
  letI : Finite (Side a b c false) := Finite.of_equiv (Fin b) (sideEquiv c false).symm
  letI : Finite (Side a b c true) := Finite.of_equiv (Fin b) (sideEquiv c true).symm
  rw [← Nat.card_congr (endsEquiv (b:=b) ha c), Nat.card_sum,
    Nat.card_congr (sideEquiv (b:=b) c false), Nat.card_congr (sideEquiv (b:=b) c true)]
  simp [two_mul]

theorem card_slots (c : Cell (Fin a) K) : Nat.card (SlotFiber (b:=b) c) = b*2^a := by
  let eq := (fullSlotChart (balancedMask (K:=K) a b))
  let e : SlotFiber (b:=b) c ≃ Fin (b*2^a) :=
    { toFun := fun z => (eq z.val).2
      invFun := fun i => ⟨eq.symm (c,i), by
        rw [← fullSlotChart_cell]; exact congrArg Prod.fst (eq.apply_symm_apply (c,i))⟩
      left_inv := by
        intro z
        apply Subtype.ext
        apply eq.injective
        rw [eq.apply_symm_apply]
        exact Prod.ext z.prop.symm rfl
      right_inv := by
        intro i
        exact congrArg Prod.snd (eq.apply_symm_apply (c,i)) }
  simpa only [Nat.card_fin] using Nat.card_congr e

section Complete

variable {X Y : Type*} [Fintype X] [Fintype Y]

private def embedByCard {U V : Type*} [Fintype U] [Fintype V]
    (h : Nat.card U ≤ Nat.card V) : U ↪ V :=
  (Fintype.equivFin U).toEmbedding.trans
    ((Fin.castLEEmb (by simpa only [Nat.card_eq_fintype_card] using h)).trans
      (Fintype.equivFin V).symm.toEmbedding)

/-- Given endpoint slots and a large enough distinguished subset, fill all
endpoints by distinguished items; fill every other real item injectively
in non-endpoint slots. Unoccupied slots are padding. -/
theorem complete (good : X → Prop) (endp : Y → Prop)
    (cap : Nat.card X ≤ Nat.card Y)
    (endcap : Nat.card {y // endp y} ≤ Nat.card {x // good x}) :
    ∃ j : X ↪ Y, (∀ x, endp (j x) → good x) ∧
      (∀ y, endp y → ∃ x, j x = y) := by
  classical
  let take : {y // endp y} ↪ {x // good x} := embedByCard endcap
  let lift : {y // endp y} ↪ X := take.trans (Function.Embedding.subtype _)
  let scored : X → Prop := fun x => x ∈ Set.range lift
  let scoreEquiv : {y // endp y} ≃ {x // scored x} := Equiv.ofInjective lift lift.injective
  have hscored : ∀ x, scored x → good x := by
    rintro x ⟨y,hy⟩
    exact hy ▸ (take y).prop
  have hcard : Nat.card {x // ¬ scored x} ≤ Nat.card {y // ¬ endp y} := by
    have h1 := Nat.card_congr (Equiv.sumCompl scored)
    have h2 := Nat.card_congr (Equiv.sumCompl endp)
    rw [Nat.card_sum, ← Nat.card_congr scoreEquiv] at h1
    rw [Nat.card_sum] at h2
    omega
  let other : {x // ¬ scored x} ↪ {y // ¬ endp y} := embedByCard hcard
  let j := (Equiv.sumCompl scored).symm.toEmbedding.trans
    ((scoreEquiv.symm.toEmbedding.sumMap other).trans (Equiv.sumCompl endp).toEmbedding)
  have hyes (x : X) (hx : scored x) : j x = (scoreEquiv.symm ⟨x,hx⟩).val := by
    have h : (Equiv.sumCompl scored).symm x = Sum.inl ⟨x,hx⟩ := by
      apply (Equiv.sumCompl scored).injective
      rw [Equiv.apply_symm_apply]
      rfl
    dsimp [j]
    rw [h]
    rfl
  have hno (x : X) (hx : ¬scored x) : j x = (other ⟨x,hx⟩).val := by
    have h : (Equiv.sumCompl scored).symm x = Sum.inr ⟨x,hx⟩ := by
      apply (Equiv.sumCompl scored).injective
      rw [Equiv.apply_symm_apply]
      rfl
    dsimp [j]
    rw [h]
    rfl
  refine ⟨j, ?_, ?_⟩
  · intro x hx
    by_cases hs : scored x
    · exact hscored x hs
    · rw [hno x hs] at hx
      exact ((other ⟨x,hs⟩).prop hx).elim
  · intro y hy
    let z := scoreEquiv ⟨y,hy⟩
    exact ⟨z.val,(hyes z.val z.prop).trans (congrArg Subtype.val (scoreEquiv.symm_apply_apply ⟨y,hy⟩))⟩

end Complete

variable {W : Type*} [Fintype W]

/-- Typed packet seating. All real wires are injected into actual physical
packet positions. Both literal endpoints are real and come from the
matching, and all graph labels are preserved. -/
theorem packet_seating [Fintype K] (ha : 0 < a) (label : W → Cell (Fin a) K) (good : W → Prop)
    (cap : ∀ c, Nat.card {w // label w = c} ≤ b*2^a)
    (endcap : ∀ c, 2*b ≤ Nat.card {w : {w // label w = c} // good w.val}) :
    ∃ j : W ↪ Physical a b K,
      (∀ w, physicalCell (balancedMask a b) (j w) = label w) ∧
      (∀ w, isEnd (j w) → good w) ∧
      (∀ s, isEnd s → ∃ w, j w = s) := by
  classical
  have hloc (c : Cell (Fin a) K) :=
    complete (fun w : {w // label w = c} => good w.val)
      (fun s : SlotFiber (b:=b) c => isEnd s.val)
      ((cap c).trans_eq (card_slots (b:=b) c).symm)
      ((card_ends (b:=b) ha c).trans_le (endcap c))
  choose j hj hk using hloc
  let pack : W → Physical a b K := fun w => (j (label w) ⟨w,rfl⟩).val
  have hpres (w : W) : physicalCell (balancedMask a b) (pack w) = label w :=
    (j (label w) ⟨w,rfl⟩).prop
  have hsame (c : Cell (Fin a) K) (w : {w // label w = c}) : pack w.val = (j c w).val := by
    rcases w with ⟨w,hw⟩
    cases hw
    rfl
  refine ⟨⟨pack,?_⟩,hpres,fun w hw => hj (label w) ⟨w,rfl⟩ hw,?_⟩
  · intro x y he
    have hc := (hpres x).symm.trans ((congrArg (physicalCell (balancedMask a b)) he).trans (hpres y))
    have inj : ∀ (c : Cell (Fin a) K) (x y : {w // label w = c}),
        (j c x).val = (j c y).val → x.val = y.val :=
      fun c x y h => congrArg Subtype.val ((j c).injective (Subtype.ext h))
    apply inj (label x) ⟨x,rfl⟩ ⟨y,hc.symm⟩
    exact he.trans (hsame (label x) ⟨y,hc.symm⟩)
  · intro s hs
    let c := physicalCell (balancedMask a b) s
    obtain ⟨w,hw⟩ := hk c ⟨s,rfl⟩ hs
    refine ⟨w.val,?_⟩
    change pack w.val = s
    exact (hsame c w).trans (congrArg Subtype.val hw)

#print axioms sideEquiv
#print axioms endsEquiv
#print axioms card_ends
#print axioms card_slots
#print axioms complete
#print axioms packet_seating

end
end J7SeatPacking
