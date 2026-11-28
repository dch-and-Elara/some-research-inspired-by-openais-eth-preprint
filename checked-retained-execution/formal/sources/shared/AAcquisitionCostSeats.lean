import Acquisition

/-! A4 local address compiler from the supplied *full* physical packing.
The single predecessor lookup is derived from the literal Cauchy mesh,
not supplied as an independently asserted relation. -/

namespace AAcquisitionCost
open Acquisition

section Seats
variable {P W : Type*} {L : ℕ}

def slotPred (x : P × Fin L) : Option (P × Fin L) :=
  if h : 0 < x.2.val then
    some (x.1, ⟨x.2.val-1, by
      have hx := x.2.isLt
      omega⟩)
  else none

theorem slotPred_spec (x y : P × Fin L) :
    slotPred x = some y ↔ x.1 = y.1 ∧ (y.2.val:ℤ)+1 = x.2.val := by
  unfold slotPred
  split <;> rename_i h
  · constructor
    · intro eq
      have e := Option.some.inj eq
      have ef := congrArg (fun z : P × Fin L => z.1) e
      refine ⟨ef,?_⟩
      have ep := congrArg (fun z : P × Fin L => z.2.val) e
      dsimp only at ep
      omega
    · rintro ⟨hp,hs⟩
      apply congrArg Option.some
      exact Prod.ext hp (Fin.ext (by dsimp only; omega))
  · constructor
    · intro eq
      cases eq
    · rintro ⟨_,hs⟩
      omega

def wirePred (seat : W ≃ P × Fin L) (w : W) : Option W :=
  (slotPred (seat w)).map seat.symm

def packetOf (seat : W ≃ P × Fin L) (w : W) : P := (seat w).1
def positionOf (seat : W ≃ P × Fin L) (w : W) : ℤ := (seat w).2.val

theorem wirePred_spec (seat : W ≃ P × Fin L) (x y : W) :
    wirePred seat x = some y ↔ packetOf seat x = packetOf seat y ∧
      positionOf seat y + 1 = positionOf seat x := by
  unfold wirePred packetOf positionOf
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨v,hv,he⟩
    have hv' : v = seat y := by rw [← he, Equiv.apply_symm_apply]
    rw [hv'] at hv
    exact (slotPred_spec _ _).1 hv
  · intro h
    exact ⟨seat y, (slotPred_spec _ _).2 h, seat.symm_apply_apply y⟩

theorem wirePred_nonreuse (seat : W ≃ P × Fin L) {x y w : W}
    (hx : wirePred seat x = some w) (hy : wirePred seat y = some w) : x = y := by
  obtain ⟨px,lx⟩ := (wirePred_spec seat x w).1 hx
  obtain ⟨py,ly⟩ := (wirePred_spec seat y w).1 hy
  apply seat.injective
  refine Prod.ext (px.trans py.symm) (Fin.ext ?_)
  have h := lx.symm.trans ly
  change ((seat x).2.val : ℤ) = ((seat y).2.val : ℤ) at h
  exact_mod_cast h

theorem wirePred_literal_argument {K : Type*} [CommRing K]
    [Fintype W] [DecidableEq W] [DecidableEq P] (hL : 0 < L)
    (seat : W ≃ P × Fin L) (X : W → Bool) (x : W) :
    (∑ y : W, (packetMeshKernel L (packetOf seat) (positionOf seat) x y : K) * bit (X y)) =
      -bit (readPredecessor (wirePred seat x) X) :=
  packetMesh_argument L hL _ _ _ (wirePred_spec seat) X x

end Seats

section Literal

variable {E V₂ V₃ U C P : Type*} {L : ℕ}

abbrev LiteralWires := Acquisition.CoverOccurrences V₂ V₃ U × Bool

def unaryWire (u : U) : LiteralWires (V₂ := V₂) (V₃ := V₃) (U := U) :=
  (⟨.inr (.inr (.inr u)), ()⟩,true)

theorem unaryWire_injective :
    Function.Injective (unaryWire (V₂ := V₂) (V₃ := V₃) (U := U)) := by
  intro u v he
  have h := congrArg (fun x : LiteralWires (V₂ := V₂) (V₃ := V₃) (U := U) => x.1.1) he
  simpa only [unaryWire,Sum.inr.injEq] using h

def sparePort (cols : CoverOccurrences V₂ V₃ U ≃ CoverCol E V₃ C)
    (w : LiteralWires (V₂ := V₂) (V₃ := V₃) (U := U)) : Option (C × Bool) :=
  match cols w.1 with
  | .inr (.inr c) => some (c,w.2)
  | _ => none

theorem sparePort_spec (cols : CoverOccurrences V₂ V₃ U ≃ CoverCol E V₃ C)
    (w : LiteralWires (V₂ := V₂) (V₃ := V₃) (U := U)) (c : C) (b : Bool) :
    sparePort cols w = some (c,b) ↔ cols w.1 = .inr (.inr c) ∧ w.2 = b := by
  unfold sparePort
  cases h : cols w.1 with
  | inl e => simp
  | inr v =>
    cases v with
    | inl a => simp
    | inr c' => simp [Prod.mk.injEq]

def compiledSpare
    (seat : (CoverOccurrences V₂ V₃ U × Bool) ≃ P × Fin L)
    (cols : CoverOccurrences V₂ V₃ U ≃ CoverCol E V₃ C) (u : U) : Option (C × Bool) :=
  (wirePred seat (unaryWire u)).bind (sparePort cols)

def compiledStray
    (seat : (CoverOccurrences V₂ V₃ U × Bool) ≃ P × Fin L)
    (cols : CoverOccurrences V₂ V₃ U ≃ CoverCol E V₃ C) (u : U) : Option C :=
  (compiledSpare seat cols u).map Prod.fst

theorem compiledSpare_nonreuse
    (seat : (CoverOccurrences V₂ V₃ U × Bool) ≃ P × Fin L)
    (cols : CoverOccurrences V₂ V₃ U ≃ CoverCol E V₃ C)
    (u v : U) (c : C) (b : Bool)
    (hu : compiledSpare seat cols u = some (c,b))
    (hv : compiledSpare seat cols v = some (c,b)) : u = v := by
  obtain ⟨wu,pu,eu⟩ := Option.bind_eq_some_iff.mp hu
  obtain ⟨wv,pv,ev⟩ := Option.bind_eq_some_iff.mp hv
  have h1 := (sparePort_spec cols wu c b).1 eu
  have h2 := (sparePort_spec cols wv c b).1 ev
  have h : wu = wv := Prod.ext (cols.injective (h1.1.trans h2.1.symm)) (h1.2.trans h2.2.symm)
  subst wv
  exact unaryWire_injective (wirePred_nonreuse seat pu pv)

theorem compiledStray_load_le [Fintype U] [DecidableEq C]
    (seat : (CoverOccurrences V₂ V₃ U × Bool) ≃ P × Fin L)
    (cols : CoverOccurrences V₂ V₃ U ≃ CoverCol E V₃ C) (c : C) :
    unaryLoad (compiledStray seat cols) c ≤ 2 :=
  unaryLoad_le_two_of_ports _ _ (fun _ => rfl) (compiledSpare_nonreuse seat cols) c

theorem compiledStray_filler
    (seat : (CoverOccurrences V₂ V₃ U × Bool) ≃ P × Fin L)
    (cols : CoverOccurrences V₂ V₃ U ≃ CoverCol E V₃ C) (u : U)
    (noHard : ∀ w, wirePred seat (unaryWire u) = some w →
      ∃ c : C, cols w.1 = .inr (.inr c)) :
    (wirePred seat (unaryWire u)).map (cols ∘ Prod.fst) =
      (compiledStray seat cols u).map (fun c => .inr (.inr c)) := by
  unfold compiledStray compiledSpare
  cases h : wirePred seat (unaryWire u) with
  | none => rfl
  | some w =>
    obtain ⟨c,hc⟩ := noHard w h
    have hs := (sparePort_spec cols w c w.2).2 ⟨hc,rfl⟩
    simp [hc,hs]

variable [Fintype E] [DecidableEq E] [Fintype V₂] [DecidableEq V₂]
  [Fintype V₃] [DecidableEq V₃] [Fintype U] [DecidableEq U]
  [Fintype C] [DecidableEq C] [DecidableEq P]

theorem seatedCover_decode (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E)
    (cols : CoverOccurrences V₂ V₃ U ≃ CoverCol E V₃ C)
    (seat : (CoverOccurrences V₂ V₃ U × Bool) ≃ P × Fin L) (hL : 0 < L)
    (planted : ∀ (r : CoverRow V₂ V₃ U) (j : CoverPort r),
      (wirePred seat (⟨r,j⟩,true)).map (cols ∘ Prod.fst) =
        coverSources at₂ at₃ (compiledStray seat cols) r j)
    (even : Even (Fintype.card V₃)) {M p : ℕ}
    (hE : 2*Fintype.card E ≤ M) (hC : 2*Fintype.card C ≤ M) (hp : 2*M < p) :
    (literalMeshRegister (coverTables (K := ZMod (2^p))) cols L (packetOf seat)
      (positionOf seat)).val / publicFactor (compiledStray seat cols) = coverCount at₂ at₃ :=
  literalMeshCoverRegister_decode at₂ at₃ _ cols L hL _ _ _
    (wirePred_spec seat) planted even (compiledStray_load_le seat cols) hE hC hp

#print axioms slotPred_spec
#print axioms wirePred_nonreuse
#print axioms wirePred_literal_argument
#print axioms compiledSpare_nonreuse
#print axioms compiledStray_load_le
#print axioms compiledStray_filler
#print axioms seatedCover_decode

end Literal
end AAcquisitionCost
