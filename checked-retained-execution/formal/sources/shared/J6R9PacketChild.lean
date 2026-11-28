import J6R9PacketScopes
import J6R9PacketScaled
import J6R9PacketLocal
import LiteralPortCompiler

/-! Concrete row and source functions for the nonzero Appendix D child.
The row constant keeps the original same-group entries, while a crossing
branch reads only its target's row bit; each moment reads its actual source's
column bits. No group-local table is postulated for either function. -/
namespace J6R9PacketChild
open scoped BigOperators Polynomial Classical
open P11FullPacking J6R9PacketScopes J6R9PacketCoeff
open J6R9PacketTiles J6R9PacketLocal J6R9PacketScaled
variable {S A B R : Type*} [LinearOrder S] [CommRing R] {a b : ℕ}

noncomputable instance modeFintype (i : Fin a) (p : ℕ) (mask : MaskFamily a b S)
    [Fintype (Page a b S)] : Fintype (Mode i p mask) :=
  Fintype.ofInjective (fun m => (m.page,m.tile,m.order)) (by
    intro m n h
    cases m
    cases n
    simp_all)

abbrev RowBits (site : A → Physical a b S) (mask : MaskFamily a b S)
    (i : Fin a) (g : S) := {r : A // rowGroup mask i (site r)=g} → Bool

abbrev ColBits (site : B → Physical a b S) (mask : MaskFamily a b S)
    (i : Fin a) (g : S) := {q : B // colGroup mask i (site q)=g} → Bool

abbrev State (ρ : A → Physical a b S) (κ : B → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) (g : S) :=
  RowBits ρ mask i g × ColBits κ mask i g

noncomputable def crossNorm (mask : MaskFamily a b S) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hnil : (2:R)^p=0) (z : R) (w : Physical a b S) (m : Mode i p mask) : R := by
  classical
  exact if h : rowBlock mask i w = target mask i m then
    normalized a p hnil i.isLt.le (crossingOf ht hv (targeted_row_bit mask i w m h)) z m.order.val
    else 0

theorem off_target (mask : MaskFamily a b S) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hnil : (2:R)^p=0) (z : R) (w : Physical a b S) (m : Mode i p mask)
    (h : rowBlock mask i w ≠ target mask i m) :
    crossNorm mask i ht hv p hnil z w m = 0 := by
  simp [crossNorm,h]

theorem on_target_exact (mask : MaskFamily a b S) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hnil : (2:R)^p=0) (z : R) (w : Physical a b S) (m : Mode i p mask)
    (h : rowBlock mask i w = target mask i m) :
    (2:R)^(m.order.val+1)*crossNorm mask i ht hv p hnil z w m =
      J6R9PacketReceive.mode a p hnil i.isLt.le
        (crossingOf ht hv (targeted_row_bit mask i w m h)) z m.order.val := by
  rw [crossNorm,dif_pos h,normalized_exact]

variable [Fintype B]

noncomputable def moment (κ : B → Physical a b S) (mask : MaskFamily a b S) (i : Fin a)
    {p : ℕ} (m : Mode i p mask) (X : ColBits κ mask i (source mask i m)) : R := by
  classical
  exact ∑ q ∈ (columns (fun q => (κ q).1) (fun q => (κ q).2.val) i.val m.page m.tile.val).attach,
    (coord i.val (κ q.val).2.val:R)^m.order.val *
      bit R (X ⟨q.val,column_source_group κ mask i m q.val q.property⟩)

theorem moment_exact (κ : B → Physical a b S) (mask : MaskFamily a b S) (i : Fin a)
    {p : ℕ} (m : Mode i p mask) (X : B → Bool) :
    (moment κ mask i m (fun q => X q.val):R) =
      L (fun q => (κ q).1) (fun q => (κ q).2.val) i.val m.page m.tile.val m.order.val X := by
  classical
  unfold moment L
  let F (q : B) : R := (coord i.val (κ q).2.val:R)^m.order.val * bit R (X q)
  let C := columns (fun q => (κ q).1) (fun q => (κ q).2.val) i.val m.page m.tile.val
  change (∑ q ∈ C.attach, F q.val) = ∑ q ∈ C, F q
  exact Finset.sum_attach C F


noncomputable def localValue (κ : B → Physical a b S) (mask : MaskFamily a b S)
    (i : Fin a) (t : ℤ) (p : ℕ) (hnil : (2:R)^p=0) (z : R)
    (w : Physical a b S) (X : ColBits κ mask i (rowGroup mask i w)) : R := by
  classical
  exact ∑ q : {q : B // colGroup mask i (κ q)=rowGroup mask i w},
    if (κ q.val).1=w.1 then
      (W a t (((κ q.val).2.val:ℤ)-(w.2.val:ℤ))).eval₂ (J6ZeroTransport.reduceAt p hnil) z *
        bit R (X q)
    else 0

noncomputable def row (ρ : A → Physical a b S) (κ : B → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (hnil : (2:R)^p=0) (z : R)
    (r : A) (v : State ρ κ mask i (rowGroup mask i (ρ r))) (m : Option (Mode i p mask)) : R :=
  match m with
  | none => LiteralPortCompiler.affine (v.1 ⟨r,rfl⟩) (localValue κ mask i t p hnil z (ρ r) v.2)
  | some m => LiteralPortCompiler.slope (v.1 ⟨r,rfl⟩) * crossNorm mask i ht hv p hnil z (ρ r) m

theorem row_off_target (ρ : A → Physical a b S) (κ : B → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (hnil : (2:R)^p=0) (z : R)
    (r : A) (m : Mode i p mask) (v : State ρ κ mask i (rowGroup mask i (ρ r)))
    (h : rowBlock mask i (ρ r) ≠ target mask i m) :
    row ρ κ mask i ht hv p hnil z r v (some m)=0 := by
  simp [row,off_target mask i ht hv p hnil z (ρ r) m h]

#print axioms modeFintype
#print axioms off_target
#print axioms on_target_exact
#print axioms moment_exact
#print axioms row_off_target
end J6R9PacketChild
