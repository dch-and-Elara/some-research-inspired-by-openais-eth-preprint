import J6RecursiveOrientation
import P1DyadicGrid
import Mathlib.Tactic

/-! Read the real, oriented J6 layout rather than its ordered-cell
capacity chart. Matching is the literal signed shift inside one packet,
and any such match stays in the zero mode's native coordinate group. -/
namespace J6RecursiveOrientationLocal
open P11FullPacking P1DyadicGrid J6RecursiveOrientation
variable {S : Type*} [LinearOrder S] {a b : ℕ}

theorem template_shift_local (mask : MaskFamily a b S) (page : Page a b S)
    (x y : Fin (2^a)) (i : Fin a) (t : ℤ) (ht : t≠0)
    (hv : padicValInt 2 t=i.val) (hs : (y.val:ℤ)-(x.val:ℤ)=t) :
    (physicalCell mask (page,x) i).1 = (physicalCell mask (page,y) i).2 := by
  have hb := shifted_bit_flip ht hv hs
  by_cases he : (page.1.val i).1 ≠ (page.1.val i).2
  · cases hm : mask page.1 page.2 ⟨i,he⟩ <;> cases hx : x.val.testBit i.val <;>
      simp [physicalCell,cell,he,slotOrient,shiftMask,bits,hm,hx,hb]
  · simpa [physicalCell,cell,he] using (not_ne_iff.mp he)

noncomputable def placement (mask : MaskFamily a b S)
    (w : Fin a → S) (m l : ℕ) (h : m ≤ b) (hL : 2*l=2^a) :
    J6PhysicalPacking.Wire (diagonal w) m b l ≃ Physical a b S :=
  Equiv.ofBijective (oriented mask w m l h hL)
    ⟨orientation_injective mask w m l h hL,orientation_surjective mask w m l h hL⟩

noncomputable def shifted (mask : MaskFamily a b S)
    (w : Fin a → S) (m l : ℕ) (h : m ≤ b) (hL : 2*l=2^a) (t : ℕ)
    (p : J6PhysicalPacking.Wire (diagonal w) m b l) :
    Option (J6PhysicalPacking.Wire (diagonal w) m b l) :=
  let e := placement mask w m l h hL
  let z := e p
  if ht : z.2.val+t<2^a then some (e.symm (z.1,⟨z.2.val+t,ht⟩)) else none

theorem exact_shift (mask : MaskFamily a b S)
    (w : Fin a → S) (m l : ℕ) (h : m ≤ b) (hL : 2*l=2^a) (t : ℕ)
    (p q : J6PhysicalPacking.Wire (diagonal w) m b l)
    (hs : shifted mask w m l h hL t p = some q) :
    let z := oriented mask w m l h hL p
    let r := oriented mask w m l h hL q
    z.1=r.1 ∧ z.2.val+t=r.2.val := by
  let e := placement mask w m l h hL
  let z := e p
  let r := e q
  change z.1=r.1 ∧ z.2.val+t=r.2.val
  change (if ht : z.2.val+t<2^a then some (e.symm (z.1,⟨z.2.val+t,ht⟩)) else none) = _ at hs
  split_ifs at hs with ht
  · have he := congrArg e (Option.some.inj hs)
    rw [e.apply_symm_apply] at he
    have h₁ := congrArg (fun q : Physical a b S => q.1) he
    have h₂ := congrArg (fun q : Physical a b S => q.2.val) he
    exact ⟨h₁,h₂⟩

/-- The original printed read has no cross-group dependence on the
repaired, physical layout, at every nonzero matching level. -/
theorem shifted_local (mask : MaskFamily a b S) (w : Fin a → S)
    (m l : ℕ) (h : m ≤ b) (hL : 2*l=2^a) (t : ℕ) (ht : t≠0)
    (i : Fin a) (hv : padicValInt 2 (t:ℤ)=i.val)
    (p q : J6PhysicalPacking.Wire (diagonal w) m b l)
    (hs : shifted mask w m l h hL t p=some q) :
    (physicalCell mask (oriented mask w m l h hL p) i).1 =
      (physicalCell mask (oriented mask w m l h hL q) i).2 := by
  let z := oriented mask w m l h hL p
  let r := oriented mask w m l h hL q
  obtain ⟨hp,hind⟩ := exact_shift mask w m l h hL t p q hs
  change z.2.val+t=r.2.val at hind
  have hT : (t:ℤ)≠0 := by exact_mod_cast ht
  have hD : (r.2.val:ℤ)-(z.2.val:ℤ)=(t:ℤ) := by omega
  change (physicalCell mask (z.1,z.2) i).1=(physicalCell mask (r.1,r.2) i).2
  rw [← hp]
  exact template_shift_local mask z.1 z.2 r.2 i t hT hv hD

theorem no_padding_on_planted_page (mask : MaskFamily a b S) (w : Fin a → S)
    (m l : ℕ) (h : m ≤ b) (hL : 2*l=2^a)
    (i : Fin m) (j : Fin (2*l))
    (p : J6PhysicalPacking.Pad (diagonal w) m b l) (side : Bool) :
    (oriented mask w m l h hL (.inr (p,side))).1 ≠
      (oriented mask w m l h hL (.inl (i,j))).1 := by
  intro hp
  let z := oriented mask w m l h hL (.inr (p,side))
  let j' := Fin.cast hL.symm z.2
  have hp' : z.1=(diagonalSlot w (Fin.castLE h i) (Fin.cast hL j')).1 := by
    change z.1=(oriented mask w m l h hL (.inl (i,j))).1 at hp
    rwa [oriented_plant] at hp
  have he : z=oriented mask w m l h hL (.inl (i,j')) := by
    rw [oriented_plant]
    exact Prod.ext hp' (Fin.ext rfl)
  have hn := orientation_injective mask w m l h hL he
  cases hn

#print axioms no_padding_on_planted_page
#print axioms template_shift_local
#print axioms exact_shift
#print axioms shifted_local
end J6RecursiveOrientationLocal
