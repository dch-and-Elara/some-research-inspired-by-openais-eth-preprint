import P9SeatPhysical

namespace Paper6JointSeating
open P11FullPacking P9BalancedChart

private theorem fillSet {W : Type*} [DecidableEq W]
    (r pool : Finset W) (b : ℕ) (hr : r.card ≤ b) (hp : b - r.card ≤ pool.card)
    (hd : Disjoint r pool) :
    ∃ s : Finset W, r ⊆ s ∧ s ⊆ r ∪ pool ∧ s.card = b := by
  obtain ⟨q,hq,hqc⟩ := Finset.exists_subset_card_eq hp
  have hd' : Disjoint r q := hd.mono_right hq
  refine ⟨r ∪ q,Finset.subset_union_left,Finset.union_subset_union Finset.Subset.rfl hq,?_⟩
  rw [Finset.card_union_of_disjoint hd', hqc]
  omega

theorem fillEndpointSets {W C R : Type*} [DecidableEq W]
    (label : W → C) (row : W → R) (nonpin : W → Prop)
    (r0 r1 pool0 pool1 : C → Finset W) (b : ℕ)
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
    ∃ s0 s1 : C → Finset W,
      (∀ c, r0 c ⊆ s0 c ∧ r1 c ⊆ s1 c ∧ Disjoint (s0 c) (s1 c) ∧
        (s0 c).card = b ∧ (s1 c).card = b) ∧
      (∀ c w, w ∈ s0 c ∨ w ∈ s1 c → label w = c ∧ nonpin w) ∧
      Set.InjOn row {w | w ∈ s0 (label w)} := by
  classical
  choose s0 rs0 hs0 cs0 using fun c => fillSet (r0 c) (pool0 c) b
    (sizeR0 c) (size0 c) (avoid0 c)
  have dest0 (c : C) (w : W) (h : w ∈ s0 c) : w ∈ r0 c ∨ w ∈ pool0 c :=
    Finset.mem_union.mp (hs0 c h)
  have disj0r1 (c : C) : Disjoint (s0 c) (r1 c) := by
    apply Finset.disjoint_left.mpr
    intro w h0 h1
    rcases dest0 c w h0 with hr | hp
    · exact Finset.disjoint_left.mp (rd c) hr h1
    · exact Finset.disjoint_left.mp (avoid1 c) h1 hp
  let free (c : C) := pool1 c \ (s0 c ∪ r1 c)
  have sfree (c : C) : b - (r1 c).card ≤ (free c).card := by
    have h1 : (pool1 c ∩ (s0 c ∪ r1 c)).card ≤ (s0 c ∪ r1 c).card :=
      Finset.card_le_card Finset.inter_subset_right
    have h2 := Finset.card_union_le (s0 c) (r1 c)
    have h3 := Finset.card_sdiff_add_card_inter (s:=pool1 c) (t:=s0 c ∪ r1 c)
    rw [cs0 c] at h2
    have h4 := size1 c
    have h5 := sizeR1 c
    dsimp [free]
    omega
  have fdisj (c : C) : Disjoint (r1 c) (free c) := by
    apply Finset.disjoint_left.mpr
    intro w hw hf
    exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_union_right _ hw)
  choose s1 rs1 hs1 cs1 using fun c => fillSet (r1 c) (free c) b
    (sizeR1 c) (sfree c) (fdisj c)
  refine ⟨s0,s1,?_,?_,?_⟩
  · intro c
    refine ⟨rs0 c,rs1 c,Finset.disjoint_left.mpr ?_,cs0 c,cs1 c⟩
    intro w h0 h1
    rcases Finset.mem_union.mp (hs1 c h1) with hr | hf
    · exact Finset.disjoint_left.mp (disj0r1 c) h0 hr
    · exact (Finset.mem_sdiff.mp hf).2 (Finset.mem_union_left _ h0)
  · intro c w hw
    apply labels c w
    rcases hw with h0 | h1
    · rcases dest0 c w h0 with hr | hp
      · exact Or.inl hr
      · exact Or.inr (Or.inr (Or.inl hp))
    · rcases Finset.mem_union.mp (hs1 c h1) with hr | hf
      · exact Or.inr (Or.inl hr)
      · exact Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.mp hf).1))
  · intro x hx y hy he
    rcases dest0 _ x hx with hxr | hxp <;> rcases dest0 _ y hy with hyr | hyp
    · exact rowR hxr hyr he
    · exact False.elim (rowApart x y hxr hyp he)
    · exact False.elim (rowApart y x hyr hxp he.symm)
    · exact rowP hxp hyp he

#print axioms fillEndpointSets
end Paper6JointSeating

