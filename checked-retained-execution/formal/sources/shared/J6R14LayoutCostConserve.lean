import J6R14LayoutCostSource

/-! Reordering cannot drop a physical incidence, and classification
does not identify parallel edges. The partition/permutation proof
uses disjoint actual ordered keys, not a presumed correct sorter. -/
namespace J6R14LayoutCost
open J6R12CollisionEdges J6R12CollisionSource J6R12CollisionGreedyStep

def flattened {X : Type*} (view : X→EdgeTape) (es : List X) (ks : List CellWord) : List X :=
  ks.flatMap (fun k => bucket view k es)

theorem flattened_missing {X : Type*} (view : X→EdgeTape) (x : X) (es : List X)
    (k : CellWord) (hk : rawCell (view x)=some k) (ks : List CellWord) (h : k∉ks) :
    flattened view (x::es) ks=flattened view es ks := by
  induction ks with
  | nil => rfl
  | cons l ls ih =>
    have h₁ : k≠l := fun H => h (H ▸ List.mem_cons_self)
    have h₂ : k∉ls := fun H => h (List.mem_cons_of_mem _ H)
    change bucket view l (x::es)++flattened view (x::es) ls=
      bucket view l es++flattened view es ls
    rw [ih h₂]
    simp [bucket,hk,h₁]

theorem flattened_cons {X : Type*} (view : X→EdgeTape) (x : X) (es : List X)
    (k : CellWord) (hk : rawCell (view x)=some k) (ks : List CellWord)
    (hn : ks.Nodup) (h : k∈ks) :
    (flattened view (x::es) ks).Perm (x::flattened view es ks) := by
  induction ks with
  | nil => simp at h
  | cons l ls ih =>
    obtain ⟨hm,hs⟩ := List.nodup_cons.mp hn
    change (bucket view l (x::es)++flattened view (x::es) ls).Perm
      (x::(bucket view l es++flattened view es ls))
    by_cases e : k=l
    · subst l
      rw [flattened_missing view x es k hk ls hm]
      simp [bucket,hk]
    · have hl : k∈ls := (List.mem_cons.mp h).resolve_left e
      have hb : bucket view l (x::es)=bucket view l es := by simp [bucket,hk,e]
      rw [hb]
      exact ((ih hs hl).append_left _).trans List.perm_middle

theorem flattened_exact {X : Type*} (view : X→EdgeTape) (es : List X)
    (ks : List CellWord) (hn : ks.Nodup)
    (h : ∀ e∈es, ∃ k∈ks,rawCell (view e)=some k) :
    (flattened view es ks).Perm es := by
  induction es with
  | nil => simp [flattened,bucket]
  | cons e es ih =>
    obtain ⟨k,hK,hE⟩ := h e List.mem_cons_self
    exact (flattened_cons view e es k hE ks hn hK).trans
      (List.Perm.cons _ (ih (fun x hx => h x (List.mem_cons_of_mem _ hx))))

theorem graph_grouped_conserves {E R C A : Type*} [Fintype E] [Fintype A]
    (F : Format E R C A) (z : R⊕C→A) (q : ℕ) :
    let es := F.graph (fun x => some (z x))
    let bs := (allPairs F.b).map (boxSpec Tagged.edge q (tagSpec q 0 es))
    (bs.flatMap Box.rows).Perm (tagSpec q 0 es) := by
  let es := F.graph (fun x => some (z x))
  change (((allPairs F.b).map (boxSpec Tagged.edge q (tagSpec q 0 es))).flatMap Box.rows).Perm _
  rw [List.flatMap_map]
  change (flattened Tagged.edge (tagSpec q 0 es) (allPairs F.b)).Perm _
  apply flattened_exact _ _ _ (allPairs_nodup _)
  intro e he
  have H : e.edge∈es := by
    rw [← tagSpec_edge q 0 es]
    exact List.mem_map.mpr ⟨e,he,rfl⟩
  obtain ⟨w,_,hw⟩ := List.mem_map.mp H
  refine ⟨codePair F (sourceCell F z w),codePair_mem F _,?_⟩
  change graphWord F z w=e.edge at hw
  rw [← hw,graphWord_cell]

#print axioms flattened_exact
#print axioms graph_grouped_conserves
end J6R14LayoutCost



