import J6PhysicalPacking
import P11FullPackingPlacement
import Mathlib.Tactic

/-! J6 padding orientation repair. The ordered-cell chart is first
converted to the printed packet chart, with an explicit diagonal chart
so the planted layer order does not change. The two padding ports are not
presumed to be adjacent in the printed packet. -/
namespace J6RecursiveOrientation
open P11FullPacking
variable {S : Type*} [LinearOrder S] {a b : ℕ}

def diagonal (w : Fin a → S) : Cell (Fin a) S := fun i => (w i,w i)

theorem diagonal_no_hot (w : Fin a → S) : IsEmpty (Hot (key (diagonal w))) :=
  ⟨fun i => i.property (by simp [key,diagonal,sortPair])⟩

theorem diagonal_cell (w : Fin a → S) (v : Orient (key (diagonal w))) :
    cell (key (diagonal w)) v = diagonal w := by
  have hv : v = orientation (diagonal w) := by
    funext i
    exact (diagonal_no_hot w).false i |>.elim
  rw [hv,cell_decode]

def diagonalSlot (w : Fin a → S) (p : Fin b) (x : Fin (2^a)) : Physical a b S :=
  (⟨key (diagonal w),(p,orientation (diagonal w))⟩,x)

theorem diagonalSlot_cell (mask : MaskFamily a b S) (w : Fin a → S)
    (p : Fin b) (x : Fin (2^a)) :
    physicalCell mask (diagonalSlot w p x) = diagonal w :=
  diagonal_cell w _

abbrev Fibre (mask : MaskFamily a b S) (c : Cell (Fin a) S) :=
  {z : Physical a b S // physicalCell mask z=c}

def diagonalFibre (mask : MaskFamily a b S) (w : Fin a → S) :
    (Fin b × Fin (2^a)) ≃ Fibre mask (diagonal w) where
  toFun p := ⟨diagonalSlot w p.1 p.2,diagonalSlot_cell mask w p.1 p.2⟩
  invFun z := (z.val.1.2.1,z.val.2)
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟨k,p,v⟩,x⟩,hx⟩
    have hk : k = key (diagonal w) := by
      have h := congrArg key hx
      exact (key_cell k _).symm.trans h
    subst k
    have hv : v = orientation (diagonal w) := by
      funext i
      exact (diagonal_no_hot w).false i |>.elim
    subst v
    rfl

noncomputable def arbitraryFibre (mask : MaskFamily a b S) (c : Cell (Fin a) S) :
    (Fin b × Fin (2^a)) ≃ Fibre mask c := by
  let e := fullSlotChart mask
  let r : (Fin (b*2^a)) ≃ Fibre mask c :=
    { toFun x := ⟨e.symm (c,x),by
        have h := congrArg Prod.fst (e.apply_symm_apply (c,x))
        exact h⟩
      invFun z := (e z.val).2
      left_inv x := congrArg Prod.snd (e.apply_symm_apply (c,x))
      right_inv z := Subtype.ext (e.injective (by
        rw [e.apply_symm_apply]
        exact Prod.ext z.property.symm rfl)) }
  exact finProdFinEquiv.trans r

noncomputable def alignedFibre (mask : MaskFamily a b S) (w : Fin a → S)
    (c : Cell (Fin a) S) : (Fin b × Fin (2^a)) ≃ Fibre mask c :=
  if h : c=diagonal w then h ▸ diagonalFibre mask w else arbitraryFibre mask c

theorem aligned_at_diagonal (mask : MaskFamily a b S) (w : Fin a → S)
    (p : Fin b × Fin (2^a)) :
    (alignedFibre mask w (diagonal w) p).val = diagonalSlot w p.1 p.2 := by
  unfold alignedFibre
  rw [dif_pos rfl]
  rfl

noncomputable def oriented
    (mask : MaskFamily a b S) (w : Fin a → S) (m l : ℕ) (h : m≤b)
    (hL : 2*l=2^a) (e : J6PhysicalPacking.Wire (diagonal w) m b l) : Physical a b S :=
  let c := J6PhysicalPacking.place (diagonal w) m b l h e
  (alignedFibre mask w c.1 (c.2.1,Fin.cast hL c.2.2)).val

theorem orientation_preserved
    (mask : MaskFamily a b S) (w : Fin a → S) (m l : ℕ) (h : m≤b)
    (hL : 2*l=2^a) (e : J6PhysicalPacking.Wire (diagonal w) m b l) :
    physicalCell mask (oriented mask w m l h hL e) =
      (J6PhysicalPacking.place (diagonal w) m b l h e).1 := by
  let c := J6PhysicalPacking.place (diagonal w) m b l h e
  exact (alignedFibre mask w c.1 (c.2.1,Fin.cast hL c.2.2)).property

theorem orientation_injective
    (mask : MaskFamily a b S) (w : Fin a → S) (m l : ℕ) (h : m≤b)
    (hL : 2*l=2^a) : Function.Injective (oriented mask w m l h hL) := by
  intro u v huv
  let x := J6PhysicalPacking.place (diagonal w) m b l h u
  let y := J6PhysicalPacking.place (diagonal w) m b l h v
  have hc : x.1=y.1 := by
    have hh := congrArg (physicalCell mask) huv
    simpa only [orientation_preserved] using hh
  apply J6PhysicalPacking.place_injective (diagonal w) m b l h
  change x=y
  apply Prod.ext hc
  have he :
      (alignedFibre mask w x.1 (x.2.1,Fin.cast hL x.2.2)).val =
      (alignedFibre mask w y.1 (y.2.1,Fin.cast hL y.2.2)).val := huv
  rw [← hc] at he
  have hw := (alignedFibre mask w x.1).injective (Subtype.ext he)
  have hb := congrArg (fun q : Fin b × Fin (2^a) => q.1) hw
  have hx := congrArg (fun q : Fin b × Fin (2^a) => q.2.val) hw
  exact Prod.ext hb (Fin.ext hx)

theorem oriented_plant
    (mask : MaskFamily a b S) (w : Fin a → S) (m l : ℕ) (h : m≤b)
    (hL : 2*l=2^a) (i : Fin m) (j : Fin (2*l)) :
    oriented mask w m l h hL (.inl (i,j)) =
      diagonalSlot w (Fin.castLE h i) (Fin.cast hL j) := by
  unfold oriented
  exact aligned_at_diagonal mask w _

theorem oriented_padding_same_owner
    (mask : MaskFamily a b S) (w : Fin a → S) (m l : ℕ) (h : m≤b)
    (hL : 2*l=2^a) (p : J6PhysicalPacking.Pad (diagonal w) m b l) (side : Bool) :
    physicalCell mask (oriented mask w m l h hL (.inr (p,side))) = p.1 :=
  orientation_preserved mask w m l h hL _

theorem orientation_surjective
    (mask : MaskFamily a b S) (w : Fin a → S) (m l : ℕ) (h : m≤b)
    (hL : 2*l=2^a) : Function.Surjective (oriented mask w m l h hL) := by
  intro z
  let c := physicalCell mask z
  let zz : Fibre mask c := ⟨z,rfl⟩
  let r := (alignedFibre mask w c).symm zz
  obtain ⟨e,he⟩ := J6PhysicalPacking.place_surjective (diagonal w) m b l h
    (c,r.1,Fin.cast hL.symm r.2)
  refine ⟨e,?_⟩
  unfold oriented
  rw [he]
  change (alignedFibre mask w c (r.1,Fin.cast hL (Fin.cast hL.symm r.2))).val = z
  have hc : Fin.cast hL (Fin.cast hL.symm r.2) = r.2 := Fin.ext rfl
  rw [hc]
  exact congrArg Subtype.val ((alignedFibre mask w c).apply_symm_apply zz)

#print axioms orientation_surjective
#print axioms diagonalFibre
#print axioms orientation_preserved
#print axioms orientation_injective
#print axioms oriented_plant
#print axioms oriented_padding_same_owner
end J6RecursiveOrientation
