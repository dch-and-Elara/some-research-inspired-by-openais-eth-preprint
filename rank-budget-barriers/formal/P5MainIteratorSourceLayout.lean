import P5MainIteratorLabels
import P5MainIteratorOccupied

/-! Source realization: actual variable and factor words, actual
occurrences and distinct (copy, cell) addresses. -/
namespace P5MainIterator
open scoped BigOperators Classical

variable {E V F Copy I B : Type*} [Fintype E] [Fintype V] [Fintype F]
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

abbrev CopyOrbit (Copy I B : Type*) [LinearOrder B] := Copy × (I → SortedPair B)

abbrev CoordFamily (o : CopyOrbit Copy I B) := Unequal o.2

abbrev CopiedSlot (Copy I B : Type*) [LinearOrder B] := Σ o : CopyOrbit Copy I B, CoordFamily o → Bool

def copyEncode (s : Copy × WordCell I B) : CopiedSlot Copy I B :=
  ⟨(s.1,orbitKey s.2),(encodeOrbit s.2).2⟩

noncomputable def copyDecode (s : CopiedSlot Copy I B) : Copy × WordCell I B :=
  (s.1.1,decodeOrbit ⟨s.1.2,s.2⟩)

omit [Fintype Copy] [Fintype I] [Fintype B] in
theorem copy_decode_encode (s : Copy × WordCell I B) : copyDecode (copyEncode s) = s := by
  exact Prod.ext rfl (decode_encodeOrbit s.2)

omit [Fintype Copy] [Fintype I] [Fintype B] in
theorem copyEncode_injective : Function.Injective (copyEncode (Copy:=Copy) (I:=I) (B:=B)) :=
  Function.LeftInverse.injective copy_decode_encode

/-- The real MAIN packing keeps one word per assignment variable and
one per factor, and no repeated (copy, cell) addresses. -/
structure SourceLayout (E V F Copy I B : Type*) [LinearOrder B] where
  placement : Placement E V (Copy × WordCell I B)
  factor : E → F
  a : V → I → B
  d : F → I → B
  first : ∀ e i, ((placement.slot e).2 i).1 = a (placement.owner e) i
  second : ∀ e i, ((placement.slot e).2 i).2 = d (factor e) i

def SourceLayout.orbitPlacement (L : SourceLayout E V F Copy I B) :
    Placement E V (CopiedSlot Copy I B) where
  owner := L.placement.owner
  occurs := L.placement.occurs
  slot := ⟨copyEncode ∘ L.placement.slot,copyEncode_injective.comp L.placement.slot.injective⟩

omit [Fintype V] [Fintype F] [Fintype Copy] [Fintype I] [Fintype B] in
/-- Same variable, copy and orbit implies the same physical incidence.
This is the only sparsity premise needed for the square-energy step. -/
theorem SourceLayout.orbit_unique (L : SourceLayout E V F Copy I B) (v : V)
    (s t : CopiedSlot Copy I B)
    (hs : s ∈ filled L.orbitPlacement v) (ht : t ∈ filled L.orbitPlacement v)
    (he : s.1=t.1) : s=t := by
  obtain ⟨x,hx,hxs⟩ := (@Finset.mem_image _ _ (Classical.decEq _) _ _ _).mp hs
  obtain ⟨y,hy,hyt⟩ := (@Finset.mem_image _ _ (Classical.decEq _) _ _ _).mp ht
  have h₀ : L.placement.owner x=L.placement.owner y :=
    ((Finset.mem_filter.mp hx).2).trans ((Finset.mem_filter.mp hy).2).symm
  have he' : (copyEncode (L.placement.slot x)).1 = (copyEncode (L.placement.slot y)).1 := by
    exact (congrArg Sigma.fst hxs).trans (he.trans (congrArg Sigma.fst hyt).symm)
  have hs' : L.placement.slot x=L.placement.slot y := by
    have hcp : (L.placement.slot x).1=(L.placement.slot y).1 := congrArg (fun o : CopyOrbit Copy I B => o.1) he'
    have hok : orbitKey (L.placement.slot x).2=orbitKey (L.placement.slot y).2 := congrArg (fun o : CopyOrbit Copy I B => o.2) he'
    refine Prod.ext hcp ?_
    refine first_and_orbit_injective _ _ (fun i => ?_) hok
    rw [L.first x i,L.first y i,h₀]
  exact hxs.symm.trans ((congrArg copyEncode hs').trans hyt)

omit [LinearOrder B] in
theorem card_wordCells : Fintype.card (WordCell I B) = (Fintype.card B)^(2*Fintype.card I) := by
  unfold WordCell
  rw [Fintype.card_fun,Fintype.card_prod,← sq,← pow_mul]

noncomputable def cellLoad (L : SourceLayout E V F Copy I B) (u : WordCell I B) : ℕ :=
  (Finset.univ.filter fun e => (L.placement.slot e).2=u).card

omit [Fintype V] [Fintype F] [Fintype Copy] in
/-- The feasibility bound used in F.A4 is a consequence of the actual
occupancy cap. The bound does not assume group-balance. -/
theorem cap_forces_label_count (L : SourceLayout E V F Copy I B) [Nonempty E]
    (hcap : ∀ u, cellLoad L u * Fintype.card (WordCell I B) ≤ 2*Fintype.card E) :
    (Fintype.card B)^(2*Fintype.card I) ≤ 2*Fintype.card E := by
  have e := Classical.choice (inferInstance : Nonempty E)
  let u := (L.placement.slot e).2
  have hpos : 1 ≤ cellLoad L u := by
    unfold cellLoad
    exact Finset.card_pos.mpr ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  rw [←card_wordCells]
  exact (by simpa using Nat.mul_le_mul_right (Fintype.card (WordCell I B)) hpos : _ ≤ _).trans (hcap u)

#print axioms copyEncode_injective
#print axioms SourceLayout.orbit_unique
#print axioms card_wordCells
#print axioms cap_forces_label_count
end P5MainIterator
