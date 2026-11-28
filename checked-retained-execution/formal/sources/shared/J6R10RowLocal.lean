import J6R10RowFibers
import J6R9PacketRealTile
import Mathlib.Tactic

/-! Original row sum and exact exchange of printed mode sum with the
real column sum. Padding columns with zero incidence receive no Boolean bit. -/
namespace J6R10RowLocal
open scoped BigOperators Polynomial Classical
open P11FullPacking J6R9PacketScopes J6R9PacketTiles J6R9PacketLocal
open J6R9PacketChild J6R10RowFibers
variable {S Q R : Type*} [LinearOrder S] [Fintype Q] [CommRing R] {a b : ℕ}

noncomputable def columnEntry (κ : Q → Physical a b S) (t : ℤ)
    (p : ℕ) (hnil : (2:R)^p=0) (z : R) (w : Physical a b S) (q : Q) (X : Q → Bool) : R :=
  if (κ q).1=w.1 then
    (W a t (((κ q).2.val:ℤ)-(w.2.val:ℤ))).eval₂ (J6ZeroTransport.reduceAt p hnil) z * bit R (X q)
  else 0

noncomputable def originalRow (κ : Q → Physical a b S) (t : ℤ)
    (p : ℕ) (hnil : (2:R)^p=0) (z : R) (w : Physical a b S) (X : Q → Bool) : R :=
  ∑ q, columnEntry κ t p hnil z w q X

theorem local_as_filter (κ : Q → Physical a b S) (mask : MaskFamily a b S)
    (i : Fin a) (t : ℤ) (p : ℕ) (hnil : (2:R)^p=0) (z : R)
    (w : Physical a b S) (X : Q → Bool) :
    localValue κ mask i t p hnil z w (fun q => X q.val) =
      ∑ q, if colGroup mask i (κ q)=rowGroup mask i w then columnEntry κ t p hnil z w q X else 0 := by
  rw [← Finset.sum_filter]
  change (∑ q : {q : Q // colGroup mask i (κ q)=rowGroup mask i w}, columnEntry κ t p hnil z w q.val X) = _
  symm
  exact Finset.sum_subtype _ (by simp) _

/-- No assumption of a populated tile or spare slot is used in exchanging
the sum. A mode in an empty tile contributes zero automatically. -/
theorem sum_real_columns_first (κ : Q → Physical a b S) (mask : MaskFamily a b S)
    (i : Fin a) (p : ℕ) [Fintype (Page a b S)]
    (X : Q → Bool) (c : Mode i p mask→R) :
    (∑ m : Mode i p mask, c m*moment κ mask i m (fun q => X q.val)) =
      ∑ q : Q, ∑ m ∈ Finset.univ.filter (atTile mask i (κ q)),
        c m*(coord i.val (κ q).2.val:R)^m.order.val * bit R (X q) := by
  classical
  have h (m : Mode i p mask) :
      c m*moment κ mask i m (fun q => X q.val) =
        ∑ q : Q, if atTile mask i (κ q) m then
          c m*(coord i.val (κ q).2.val:R)^m.order.val * bit R (X q) else 0 := by
    rw [moment_exact,L,Finset.mul_sum,← Finset.sum_filter]
    have he : columns (fun q => (κ q).1) (fun q => (κ q).2.val) i.val m.page m.tile.val =
        Finset.univ.filter (fun q : Q => atTile mask i (κ q) m) := by
      ext q
      exact (mem_tile_iff κ mask i m q).trans (by simp)
    rw [he]
    exact Finset.sum_congr rfl (fun _ _ => (mul_assoc _ _ _).symm)
  simp only [h]
  rw [Finset.sum_comm]
  simp only [Finset.sum_filter]

#print axioms local_as_filter
#print axioms sum_real_columns_first
end J6R10RowLocal
