import S8DPacketCount

namespace S8.DChild

open scoped BigOperators
open SourceDensity

variable {W U V I A : Type*} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype A] [LinearOrder A] [Nonempty A]
  [DecidableEq U] [DecidableEq V]

def rootCell (left : W → U) (right : W → V) (L : U → I → A) (R : V → I → A)
    (w : W) : (I → A) × (I → A) :=
  (L (left w), R (right w))

def oldEndpoint (left : W → U) (right : W → V) (w : W × Bool) : U ⊕ V :=
  if w.2 then .inr (right w.1) else .inl (left w.1)

def symbol (L : U → I → A) (R : V → I → A) (i : I) : U ⊕ V → A :=
  Sum.elim (fun u => L u i) (fun v => R v i)

/-- One child edge per retained port. Opposite ends of a parent wire are
different child edges when both have group g. Parallel wires remain distinct. -/
abbrev Edge (left : W → U) (right : W → V) (L : U → I → A) (R : V → I → A)
    (i : I) (g : A) :=
  {w : W × Bool // symbol L R i (oldEndpoint left right w) = g}

def childOld (left : W → U) (right : W → V) (L : U → I → A) (R : V → I → A)
    (i : I) (g : A) (w : Edge left right L R i g) :
    {x // symbol L R i (x : U ⊕ V) = g} :=
  ⟨oldEndpoint left right w.1,w.2⟩

def childPacket {S P : Type*} (put : W ↪ P × S)
    {left : W → U} {right : W → V} {L : U → I → A} {R : V → I → A} {i : I} {g : A}
    (w : Edge left right L R i g) : P :=
  (put w.1.1).1

theorem old_degree_left (left : W → U) (right : W → V) (L : U → I → A) (R : V → I → A)
    (i : I) (g : A) (u : U) (hu : L u i = g) :
    fiberCount (childOld left right L R i g) ⟨.inl u,hu⟩ = fiberCount left u := by
  classical
  simp only [fiberCount, ← Fintype.card_subtype]
  apply Fintype.card_congr
  refine {
    toFun := fun w => ⟨w.1.1.1, ?_⟩
    invFun := fun w => ⟨⟨(w.1,false), by simpa [symbol, oldEndpoint, w.2] using hu⟩,
      Subtype.ext (by simpa [childOld, oldEndpoint] using w.2)⟩
    left_inv := ?_
    right_inv := fun _ => rfl }
  · have he := congrArg Subtype.val w.2
    change oldEndpoint left right w.1.1 = .inl u at he
    rcases w with ⟨⟨⟨e,b⟩,eh⟩,h⟩
    cases b <;> simpa [oldEndpoint] using he
  · rintro ⟨⟨⟨e,b⟩,h⟩,he⟩
    have eq := congrArg Subtype.val he
    cases b
    · rfl
    · simp [childOld, oldEndpoint] at eq

theorem old_degree_right (left : W → U) (right : W → V) (L : U → I → A) (R : V → I → A)
    (i : I) (g : A) (v : V) (hv : R v i = g) :
    fiberCount (childOld left right L R i g) ⟨.inr v,hv⟩ = fiberCount right v := by
  classical
  simp only [fiberCount, ← Fintype.card_subtype]
  apply Fintype.card_congr
  refine {
    toFun := fun w => ⟨w.1.1.1, ?_⟩
    invFun := fun w => ⟨⟨(w.1,true), by simpa [symbol, oldEndpoint, w.2] using hv⟩,
      Subtype.ext (by simpa [childOld, oldEndpoint] using w.2)⟩
    left_inv := ?_
    right_inv := fun _ => rfl }
  · have he := congrArg Subtype.val w.2
    change oldEndpoint left right w.1.1 = .inr v at he
    rcases w with ⟨⟨⟨e,b⟩,eh⟩,h⟩
    cases b <;> simpa [oldEndpoint] using he
  · rintro ⟨⟨⟨e,b⟩,h⟩,he⟩
    have eq := congrArg Subtype.val he
    cases b
    · simp [childOld, oldEndpoint] at eq
    · rfl

theorem packet_degree {P S : Type*} [DecidableEq P] [Fintype S]
    (put : W ↪ P × S)
    (left : W → U) (right : W → V) (L : U → I → A) (R : V → I → A) (i : I) (g : A)
    (p : P) :
    fiberCount (childPacket put : Edge left right L R i g → P) p ≤ 2 * Fintype.card S := by
  classical
  rw [fiberCount, ← Fintype.card_subtype]
  have inject : {w : Edge left right L R i g // childPacket put w = p} ↪ (Bool × S) :=
    ⟨fun w => (w.1.1.2,(put w.1.1.1).2), by
      intro x y h
      have hb := congrArg Prod.fst h
      have hs := congrArg Prod.snd h
      have hf := x.2.trans y.2.symm
      have hw := put.injective (Prod.ext hf hs)
      exact Subtype.ext (Subtype.ext (Prod.ext hw hb))⟩
  simpa [Fintype.card_prod] using Fintype.card_le_of_embedding inject

theorem true_port_load_le (cell : W → (I → A) × (I → A)) (Δ : ℚ)
    (cert : CollisionCertificate cell Δ) (i : I) (b : Bool) (g : A) :
    (fiberCount (fun w => (if b then (cell w).2 else (cell w).1) i) g : ℚ) ≤
      2 * Fintype.card W / Fintype.card A := by
  let f (c : (I → A) × (I → A)) := (if b then c.2 else c.1) i
  let m := Fintype.card A ^ (Fintype.card I - 1) * Fintype.card A ^ Fintype.card I
  have hreg (a : A) : fiberCount f a = m := by
    cases b
    · exact BalancedUnion.single_coordinate_fiber i a
    · exact MainIncidence.factor_symbol_fiber i a
  exact projected_port_bound cell Δ cert f m hreg g

theorem child_edge_count (left : W → U) (right : W → V) (L : U → I → A) (R : V → I → A)
    (Δ : ℚ) (cert : CollisionCertificate (rootCell left right L R) Δ)
    (i : I) (g : A) :
    (Fintype.card (Edge left right L R i g) : ℚ) ≤ 4 * Fintype.card W / Fintype.card A := by
  classical
  let edgeEquiv : Edge left right L R i g ≃
      ({w : W // L (left w) i = g} ⊕ {w : W // R (right w) i = g}) :=
    { toFun := fun w => match w with
        | ⟨(w,false),hw⟩ => .inl ⟨w,hw⟩
        | ⟨(w,true),hw⟩ => .inr ⟨w,hw⟩
      invFun := Sum.elim (fun w => ⟨(w.1,false),w.2⟩) (fun w => ⟨(w.1,true),w.2⟩)
      left_inv := by rintro ⟨⟨w,b⟩,hw⟩; cases b <;> rfl
      right_inv := by rintro (w | w) <;> rfl }
  rw [Fintype.card_congr edgeEquiv, Fintype.card_sum,
    Fintype.card_subtype, Fintype.card_subtype, Nat.cast_add]
  have h₁ := true_port_load_le _ Δ cert i false g
  have h₂ := true_port_load_le _ Δ cert i true g
  change (fiberCount (fun w => L (left w) i) g : ℚ) ≤ _ at h₁
  change (fiberCount (fun w => R (right w) i) g : ℚ) ≤ _ at h₂
  exact (add_le_add h₁ h₂).trans_eq (by ring)

/-- Recursive degree and strict shrink for positive parents, inherited by every
    mode tuple because the child incidence graph depends only on i and g. -/
theorem recursive_step (left : W → U) (right : W → V)
    (L : U → I → Fin 64) (R : V → I → Fin 64) (Δ : ℕ)
    (cert : CollisionCertificate (rootCell left right L R) Δ)
    (hL : 2 * 2 ^ Fintype.card I ≤ Δ)
    (slots : 2 ^ Fintype.card I * Fintype.card ((I → Fin 64) × (I → Fin 64)) ≤ Fintype.card W)
    (boundL : ∀ u, fiberCount left u ≤ Δ) (boundR : ∀ v, fiberCount right v ≤ Δ)
    (i : I) (g : Fin 64) :
    let pad := paddedLoad (rootCell left right L R) (2 ^ Fintype.card I)
    ∃ put : W ↪ Packet I (Fin 64) pad × (I → Bool),
      (∀ w, slotCell (put w).1.1 (put w).2 = rootCell left right L R w) ∧
      (∀ v, fiberCount (childOld left right L R i g) v ≤ Δ) ∧
      (∀ p, fiberCount (childPacket put : Edge left right L R i g → _) p ≤ Δ) ∧
      8 * Fintype.card (Edge left right L R i g) ≤ Fintype.card W := by
  obtain ⟨⟨put,cells⟩,_⟩ := certified_root_packets _ _ cert slots
  refine ⟨put,cells,?_,?_,?_⟩
  · rintro ⟨u | v, hx⟩
    · exact (old_degree_left left right L R i g u hx).trans_le (boundL u)
    · exact (old_degree_right left right L R i g v hx).trans_le (boundR v)
  · intro p
    apply (packet_degree put left right L R i g p).trans
    simpa only [Fintype.card_fun, Fintype.card_bool] using hL
  · have hc := child_edge_count left right L R _ cert i g
    norm_num only [Fintype.card_fin] at hc
    exact_mod_cast (show (8 : ℚ) * Fintype.card (Edge left right L R i g) ≤ Fintype.card W by
      linarith only [hc, Nat.cast_nonneg (Fintype.card W) (α := ℚ)])

#print axioms old_degree_left
#print axioms old_degree_right
#print axioms packet_degree
#print axioms child_edge_count
#print axioms recursive_step

end S8.DChild
