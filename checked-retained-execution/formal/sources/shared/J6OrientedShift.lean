import J6RecursiveOrientationLocal
import Mathlib.Tactic

/-! Exact shift on the corrected printed layout. It preserves the
planted wire type in all matched layers, has literal boundary misses,
and never joins a planted wire to a padding wire in either direction. -/
namespace J6OrientedShift
open P11FullPacking J6RecursiveOrientation J6RecursiveOrientationLocal
variable {S : Type*} [LinearOrder S] {a b m l : ℕ}

theorem plant_shift (mask : MaskFamily a b S) (w : Fin a → S)
    (h : m ≤ b) (hL : 2*l=2^a) (t : ℕ) (u : Fin m) (j : Fin (2*l)) :
    shifted mask w m l h hL t (.inl (u,j)) =
      if ht : j.val+t<2*l then some (.inl (u,⟨j.val+t,ht⟩)) else none := by
  let e := placement mask w m l h hL
  let p := diagonalSlot w (Fin.castLE h u) (Fin.cast hL j)
  have he : e (.inl (u,j))=p := oriented_plant mask w m l h hL u j
  change (if ht : (e (.inl (u,j))).2.val+t<2^a then
      some (e.symm ((e (.inl (u,j))).1,⟨(e (.inl (u,j))).2.val+t,ht⟩))
    else none) = _
  rw [he]
  have hh : p.2.val+t<2^a ↔ j.val+t<2*l := by
    change j.val+t<2^a ↔ j.val+t<2*l
    omega
  by_cases ht : j.val+t<2*l
  · rw [dif_pos ht,dif_pos (hh.mpr ht)]
    congr 1
    apply e.injective
    rw [e.apply_symm_apply]
    change (p.1,⟨p.2.val+t,hh.mpr ht⟩)=oriented mask w m l h hL (.inl (u,⟨j.val+t,ht⟩))
    rw [oriented_plant]
    exact Prod.ext rfl (Fin.ext rfl)
  · rw [dif_neg ht,dif_neg (mt hh.mp ht)]

theorem no_pad_to_plant (mask : MaskFamily a b S) (w : Fin a → S)
    (h : m≤b) (hL : 2*l=2^a) (t : ℕ)
    (p : J6PhysicalPacking.Pad (diagonal w) m b l) (side : Bool)
    (u : Fin m) (j : Fin (2*l)) :
    shifted mask w m l h hL t (.inr (p,side)) ≠ some (.inl (u,j)) := by
  intro hs
  exact no_padding_on_planted_page mask w m l h hL u j p side
    (exact_shift mask w m l h hL t _ _ hs).1

theorem no_plant_to_pad (mask : MaskFamily a b S) (w : Fin a → S)
    (h : m≤b) (hL : 2*l=2^a) (t : ℕ)
    (p : J6PhysicalPacking.Pad (diagonal w) m b l) (side : Bool)
    (u : Fin m) (j : Fin (2*l)) :
    shifted mask w m l h hL t (.inl (u,j)) ≠ some (.inr (p,side)) := by
  intro hs
  exact no_padding_on_planted_page mask w m l h hL u j p side
    (exact_shift mask w m l h hL t _ _ hs).1.symm

theorem successor_injective (mask : MaskFamily a b S) (w : Fin a → S)
    (h : m≤b) (hL : 2*l=2^a) (t : ℕ)
    (p r q : J6PhysicalPacking.Wire (diagonal w) m b l)
    (hp : shifted mask w m l h hL t p=some q) (hr : shifted mask w m l h hL t r=some q) :
    p=r := by
  obtain ⟨ha,ha'⟩ := exact_shift mask w m l h hL t p q hp
  obtain ⟨hb,hb'⟩ := exact_shift mask w m l h hL t r q hr
  apply orientation_injective mask w m l h hL
  refine Prod.ext (ha.trans hb.symm) (Fin.ext ?_)
  exact Nat.add_right_cancel (ha'.trans hb'.symm)

#print axioms plant_shift
#print axioms no_pad_to_plant
#print axioms no_plant_to_pad
#print axioms successor_injective
end J6OrientedShift
