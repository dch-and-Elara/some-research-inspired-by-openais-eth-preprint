import V8PooledRangeSpine

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace V8PooledRange

/-- The tree labels are literally retained. Every additional edge must meet
an outside vertex: no extra conflict may occur inside the enabled tree. -/
def hostEnds (k : ℕ) {O E : Type*} (A : Graph (Tree k ⊕ O) E) :
    Graph (Tree k ⊕ O) (TreeEdge k ⊕ E) :=
  Sum.elim (fun j b => .inl (treeEnds k j b)) A

def OutsideEdges (k : ℕ) {O E : Type*} (A : Graph (Tree k ⊕ O) E) : Prop :=
  ∀ e : E, (∃ o : O, A e false = .inr o) ∨ (∃ o : O, A e true = .inr o)

def hostEnabled (k : ℕ) {O : Type*} (w : Word k) (b : Bool) : Tree k ⊕ O → Bool :=
  Sum.elim (treeEnabled k w b) (fun _ => false)

/-- Assigning false to the split core gives a bijection, not merely an
inequality, between allowed tree markings and allowed host markings. -/
def hostIndependentEquiv (k : ℕ) {O E : Type*} (A : Graph (Tree k ⊕ O) E)
    (hx : OutsideEdges k A) (w : Word k) (b : Bool) :
    Independent (hostEnds k A) (hostEnabled k w b) ≃
      Independent (treeEnds k) (treeEnabled k w b) where
  toFun x := ⟨fun v => x.val (.inl v), ⟨fun v => x.property.1 (.inl v),
    fun e => x.property.2 (.inl e)⟩⟩
  invFun x := ⟨Sum.elim x.val (fun _ => false), by
    constructor
    · intro v
      cases v with
      | inl v => exact x.property.1 v
      | inr v => exact Or.inl rfl
    · intro e
      cases e with
      | inl e => exact x.property.2 e
      | inr e =>
        change Sum.elim x.val (fun _ : O => false) (A e false) = false ∨
          Sum.elim x.val (fun _ : O => false) (A e true) = false
        rcases hx e with (⟨o,ho⟩ | ⟨o,ho⟩)
        · rw [ho]
          exact Or.inl rfl
        · rw [ho]
          exact Or.inr rfl⟩
  left_inv x := by
    apply Subtype.ext
    funext v
    cases v with
    | inl v => rfl
    | inr v =>
      change false = x.val (.inr v)
      exact (x.property.1 (.inr v)).resolve_right (by change false ≠ true; decide) |>.symm
  right_inv _ := rfl

theorem physical_endpoint_count (k : ℕ) {O E : Type*} [Fintype O]
    (A : Graph (Tree k ⊕ O) E) (hx : OutsideEdges k A)
    (p : ThreePorts (hostEnds k A)) (w : Word k) (b : Bool) :
    satCount (hostEnds k A) p (hostEnabled k w b) = CaterpillarRange.output k (w,b) := by
  rw [five_copy_count,
    Fintype.card_congr (hostIndependentEquiv k A hx w b), tree_count]

theorem physical_endpoint_pair_injective (k : ℕ) {O E : Type*} [Fintype O]
    (A : Graph (Tree k ⊕ O) E) (hx : OutsideEdges k A)
    (p : ThreePorts (hostEnds k A)) :
    Function.Injective (fun w : Word k =>
      (satCount (hostEnds k A) p (hostEnabled k w false),
       satCount (hostEnds k A) p (hostEnabled k w true))) := by
  simpa only [physical_endpoint_count k A hx] using CaterpillarRange.output_pair_injective k

noncomputable def physicalRange {V E : Type*} [Fintype V] [DecidableEq V]
    (G : Graph V E) (p : ThreePorts G) : Finset ℕ :=
  Finset.univ.image (satCount G p)

theorem physical_range_square (k : ℕ) {O E : Type*} [Fintype O] [DecidableEq O]
    (A : Graph (Tree k ⊕ O) E) (hx : OutsideEdges k A)
    (p : ThreePorts (hostEnds k A)) :
    2^k ≤ (physicalRange (hostEnds k A) p).card ^ 2 := by
  have hsub : CaterpillarRange.attained k ⊆ physicalRange (hostEnds k A) p := by
    intro y hy
    obtain ⟨⟨w,b⟩,_,rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_image.mpr
      ⟨hostEnabled k w b, Finset.mem_univ _, physical_endpoint_count k A hx p w b⟩
  exact (CaterpillarRange.output_range_square k).trans
    (Nat.pow_le_pow_left (Finset.card_le_card hsub) 2)

theorem physical_terminal_precision {V E : Type*} [Fintype V]
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool) :
    satCount G p s < 2^(5 * Fintype.card V + 3) := by
  classical
  have h := Fintype.card_le_of_injective
    (Subtype.val : PhysicalModels G p s → (Variable V → Bool)) Subtype.val_injective
  rw [Fintype.card_fun,Fintype.card_bool,variable_count] at h
  exact h.trans_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (by omega))

/-- Pooled consequence after the native encoder has supplied the menu
alphabet bound. Side states are allowed to depend on the *whole* menu. -/
theorem physical_decoder_budget (k B b : ℕ) {O E : Type*} [Fintype O] [DecidableEq O]
    (A : Graph (Tree k ⊕ O) E) (hx : OutsideEdges k A)
    (p : ThreePorts (hostEnds k A)) {Menu : Type*} [Fintype Menu]
    (Side : Menu → Type*) [∀ m, Fintype (Side m)]
    (hmenu : Fintype.card Menu ≤ 2^B) (hside : ∀ m, Fintype.card (Side m) ≤ 2^b)
    (message : (Tree k ⊕ O → Bool) → Menu)
    (aux : (s : Tree k ⊕ O → Bool) → Side (message s))
    (decode : (Σ m, Side m) → ℕ)
    (correct : ∀ s, decode ⟨message s, aux s⟩ = satCount (hostEnds k A) p s) :
    k ≤ 2 * (B+b) := by
  have hc : (physicalRange (hostEnds k A) p).card ≤ Fintype.card (Σ m, Side m) :=
    CaterpillarRange.range_le_transcripts (satCount (hostEnds k A) p)
      (fun s => ⟨message s, aux s⟩) decode correct
  have hm : Fintype.card (Σ m, Side m) ≤ 2^(B+b) := calc
    _ = ∑ m : Menu, Fintype.card (Side m) := Fintype.card_sigma
    _ ≤ ∑ _m : Menu, 2^b := Finset.sum_le_sum (fun _ _ => hside _)
    _ = Fintype.card Menu * 2^b := by simp
    _ ≤ 2^B * 2^b := Nat.mul_le_mul_right _ hmenu
    _ = _ := (pow_add _ _ _).symm
  have hs := (physical_range_square k A hx p).trans (Nat.pow_le_pow_left (hc.trans hm) 2)
  apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
  rw [Nat.mul_comm 2 (B+b), pow_mul]
  exact hs

#print axioms hostIndependentEquiv
#print axioms physical_endpoint_count
#print axioms physical_endpoint_pair_injective
#print axioms physical_range_square
#print axioms physical_terminal_precision
#print axioms physical_decoder_budget

end V8PooledRange
