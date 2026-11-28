import V8PooledRangeSimple

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace V8PooledRange
namespace Split

/-- Place each old core split pair in its own cluster. The two caterpillar
vertices at position i join the cluster of leaf i's first deficit spoke. -/
def location (k : ℕ) : V k → Deficit k × Fin 4
  | .inl (i,false) => (.inl (i,false),2)
  | .inl (i,true) => (.inl (i,false),3)
  | .inr (c,false) => (c,0)
  | .inr (c,true) => (c,1)

theorem location_injective (k : ℕ) : Function.Injective (location k) := by
  rintro (⟨i,a⟩ | ⟨c,a⟩) (⟨j,b⟩ | ⟨d,b⟩) h <;>
    cases a <;> cases b <;> simp [location] at h ⊢
  all_goals exact h

def clusterOf (k : ℕ) (v : V k) : Deficit k := (location k v).1

def representative {k : ℕ} (f : V k → Bool) (c : Deficit k) : Bool :=
  f (.inr (c,false))

def Partial {k : ℕ} (f : V k → Bool) (c : Deficit k) : Prop :=
  ∃ v : V k, clusterOf k v = c ∧ f v ≠ representative f c

abbrev Part {X : Type*} (f : X → Bool) (b : Bool) := {v : X // f v = b}
abbrev PartialClusters {k : ℕ} (f : V k → Bool) := {c : Deficit k // Partial f c}

abbrev Cross {V E : Type*} (G : Graph V E) (f : V → Bool) :=
  {e : E // f (G e false) ≠ f (G e true)}

noncomputable instance {X : Type*} [Fintype X] (f : X → Bool) (b : Bool) :
    Fintype (Part f b) := Fintype.ofFinite _
noncomputable instance {k : ℕ} (f : V k → Bool) :
    Fintype (PartialClusters f) := Fintype.ofFinite _
noncomputable instance {V E : Type*} [Fintype E] (G : Graph V E) (f : V → Bool) :
    Fintype (Cross G f) := Fintype.ofFinite _

noncomputable def placePart {k : ℕ} (f : V k → Bool) (b : Bool) (v : Part f b) :
    (Part (representative f) b ⊕ PartialClusters f) × Fin 4 :=
  let c := clusterOf k v.val
  let z := (location k v.val).2
  if h : representative f c = b then (.inl ⟨c,h⟩,z)
  else (.inr ⟨c, ⟨v.val,rfl,fun hv => h (hv.symm.trans v.property)⟩⟩,z)

private def dropPart {k : ℕ} {f : V k → Bool} {b : Bool}
    (q : (Part (representative f) b ⊕ PartialClusters f) × Fin 4) : Deficit k × Fin 4 :=
  (q.1.elim Subtype.val Subtype.val,q.2)

private theorem drop_placePart {k : ℕ} (f : V k → Bool) (b : Bool) (v : Part f b) :
    dropPart (placePart f b v) = location k v.val := by
  unfold placePart
  dsimp only
  split <;> rfl

theorem side_card_bound {k : ℕ} (f : V k → Bool) (b : Bool) :
    Fintype.card (Part f b) ≤
      (Fintype.card (Part (representative f) b) + Fintype.card (PartialClusters f))*4 := by
  have h := Fintype.card_le_of_injective (placePart f b) (by
    intro x y heq
    apply Subtype.ext
    apply location_injective k
    rw [← drop_placePart f b x, heq, drop_placePart])
  simpa only [Fintype.card_prod,Fintype.card_sum,Fintype.card_fin] using h

theorem bad_has_internal_cross {k : ℕ} {E : Type*}
    (H : Graph (Deficit k) E) (p : ThreePorts H) (f : V k → Bool) (c : Deficit k)
    (hc : Partial f c) :
    ∃ e : Cross (graph H p) f, clusterOf k (graph H p e.val false) = c := by
  rcases hc with ⟨v,hv,hd⟩
  by_cases h : f (.inr (c,true)) = f (.inr (c,false))
  · rcases v with (⟨i,b⟩ | ⟨j,b⟩)
    · have hj : c = .inl (i,false) := by cases b <;> exact hv.symm
      subst c
      by_cases hl : f (.inl (i,true)) = f (.inr (.inl (i,false),true))
      · cases b
        · refine ⟨⟨.inl (privateLeafEdge k i),?_⟩,?_⟩
          · intro hs
            apply hd
            rw [tree_endpoint,tree_endpoint,treeEnd_leaf,treeEnd_leaf] at hs
            exact hs.trans (hl.trans h)
          · rw [tree_endpoint,treeEnd_leaf]
        · exact False.elim (hd (hl.trans h))
      · refine ⟨⟨.inr (.inr (.inr (.inl (i,false)))),?_⟩,?_⟩
        · exact hl
        · exact hj.symm
    · have hj : c = j := by cases b <;> exact hv.symm
      subst c
      cases b
      · exact False.elim (hd rfl)
      · exact False.elim (hd h)
  · refine ⟨⟨.inr (.inr (.inl c)),?_⟩,?_⟩
    · exact Ne.symm h
    · rfl

theorem partial_card_bound {k : ℕ} {E : Type*} [Fintype E]
    (H : Graph (Deficit k) E) (p : ThreePorts H) (f : V k → Bool) :
    Fintype.card (PartialClusters f) ≤ Fintype.card (Cross (graph H p) f) := by
  classical
  choose w hw using (fun c : PartialClusters f => bad_has_internal_cross H p f c.val c.property)
  apply Fintype.card_le_of_injective w
  intro x y he
  apply Subtype.ext
  rw [← hw x,he,hw y]

#print axioms location_injective
#print axioms side_card_bound
#print axioms bad_has_internal_cross
#print axioms partial_card_bound

end Split
end V8PooledRange
