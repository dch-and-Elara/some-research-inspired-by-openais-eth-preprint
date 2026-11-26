import J6R10RowLocal
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Complete physical row identity for Appendix D's nonzero probe.
On a fixed column, only its real packet/tile modes survive; otherwise the
old same-group coefficient is literally retained. -/
namespace J6R10RowIdentity
open scoped BigOperators Polynomial Classical
open P11FullPacking P1DyadicGrid J6R9PacketScopes J6R9PacketTiles
open J6R9PacketChild J6R9PacketCoeff J6R9PacketReceive J6R9PacketRealTile
open J6R10RowLocal J6R10RowClassify J6R10RowFibers
variable {S Q R : Type*} [LinearOrder S] [Fintype Q] [CommRing R] {a b : ℕ}

noncomputable def scaledRow (mask : MaskFamily a b S) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ) (hnil : (2:R)^p=0) (z : R)
    (w : Physical a b S) (m : Mode i p mask) : R :=
  (2:R)^(m.order.val+1)*crossNorm mask i ht hv p hnil z w m

omit [Fintype Q] in theorem cross_fiber_recovers_column (κ : Q → Physical a b S) (mask : MaskFamily a b S)
    (i : Fin a) {t : ℤ} (htM : t∈grid a) (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hp : 0<p) (hnil : (2:R)^p=0) (z : R) [Fintype (Page a b S)]
    (w : Physical a b S) (X : Q → Bool) (q : Q) :
      (∑ m ∈ Finset.univ.filter (atTile mask i (κ q)),
        scaledRow mask i ht hv p hnil z w m*(coord i.val (κ q).2.val:R)^m.order.val * bit R (X q)) =
      if (κ q).1=w.1 ∧ colGroup mask i (κ q)≠rowGroup mask i w then
        columnEntry κ t p hnil z w q X else 0 := by
  classical
  by_cases hc : (κ q).1=w.1 ∧ colGroup mask i (κ q)≠rowGroup mask i w
  · let d := crossingOf ht hv (cross_bit mask i w (κ q) hc.1 hc.2)
    rw [if_pos hc,exact_mode_fiber mask i p w (κ q) hc.1 hc.2]
    have hmode (n : Fin (p-1)) :
        scaledRow mask i ht hv p hnil z w (actualMode mask i w (κ q) hc.1 hc.2 n) =
          mode a p hnil i.isLt.le d z n.val := by
      unfold scaledRow
      rw [on_target_exact mask i ht hv p hnil z _ _ (actualMode_targets mask i w (κ q) hc.1 hc.2 n)]
      rfl
    change (∑ n : Fin (p-1),
      scaledRow mask i ht hv p hnil z w (actualMode mask i w (κ q) hc.1 hc.2 n) *
        (coord i.val (κ q).2.val:R)^n.val*bit R (X q)) = _
    simp only [hmode,← Finset.sum_mul]
    let f (n : ℕ) : R := mode a p hnil i.isLt.le d z n * (coord i.val (κ q).2.val:R)^n
    change (∑ n : Fin (p-1), f n.val) * bit R (X q) = _
    rw [Fin.sum_univ_eq_sum_range f (p-1)]
    have he := actual_tile_entry κ i htM ht hv p hp hnil z w (tileOf i (κ q).2)
      (cross_bit mask i w (κ q) hc.1 hc.2) q rfl
    change _ = ∑ n ∈ Finset.range (p-1), f n at he
    rw [← he]
    simp [columnEntry,hc.1]
  · rw [if_neg hc]
    refine Finset.sum_eq_zero (fun m hm => ?_)
    obtain ⟨hpage,htile⟩ := (Finset.mem_filter.mp hm).2
    have hn : rowBlock mask i w≠target mask i m := fun hs =>
      hc (target_col_cross mask i w (κ q) m hpage htile hs)
    simp [scaledRow,off_target mask i ht hv p hnil z w m hn]

theorem actual_row_eq (κ : Q → Physical a b S) (mask : MaskFamily a b S)
    (i : Fin a) {t : ℤ} (htM : t∈grid a) (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hp : 0<p) (hnil : (2:R)^p=0) (z : R) [Fintype (Page a b S)]
    (w : Physical a b S) (X : Q → Bool) :
    originalRow κ t p hnil z w X =
      localValue κ mask i t p hnil z w (fun q => X q.val) +
        ∑ m : Mode i p mask, scaledRow mask i ht hv p hnil z w m *
          moment κ mask i m (fun q => X q.val) := by
  classical
  rw [local_as_filter,sum_real_columns_first]
  simp only [cross_fiber_recovers_column κ mask i htM ht hv p hp hnil z w X,← Finset.sum_add_distrib]
  unfold originalRow
  refine Finset.sum_congr rfl (fun q _ => ?_)
  by_cases hg : colGroup mask i (κ q)=rowGroup mask i w
  · simp [hg]
  · by_cases hpage : (κ q).1=w.1
    · simp [hg,hpage]
    · simp [hg,hpage,columnEntry]

#print axioms cross_fiber_recovers_column
#print axioms actual_row_eq
end J6R10RowIdentity
