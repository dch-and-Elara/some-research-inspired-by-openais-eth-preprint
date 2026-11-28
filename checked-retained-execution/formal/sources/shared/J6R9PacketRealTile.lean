import J6R9PacketTransport
import J6R9PacketScopes
import Mathlib.Tactic

/-! Actual same-page row interaction, restricted to a crossing tile.
The equality is read in the native receiving ring, and uses the original
canceled W on every real column in that tile. -/
namespace J6R9PacketRealTile
open scoped BigOperators Polynomial
open P11FullPacking P1DyadicGrid J6R9PacketScopes J6R9PacketTiles
open J6R9PacketCoeff J6R9PacketLocal J6R9PacketReceive J6R9PacketTransport
variable {S Q R : Type*} [LinearOrder S] [Fintype Q] [CommRing R] {a b : ℕ}

theorem difference_mem_grid (x y : Fin (2^a)) : (y.val:ℤ)-(x.val:ℤ)∈grid a := by
  rw [mem_grid]
  have hx : (x.val:ℤ)<pow₂ a := by
    unfold pow₂
    exact_mod_cast x.isLt
  have hy : (y.val:ℤ)<pow₂ a := by
    unfold pow₂
    exact_mod_cast y.isLt
  have hx0 : 0≤(x.val:ℤ) := Int.natCast_nonneg _
  have hy0 : 0≤(y.val:ℤ) := Int.natCast_nonneg _
  omega

omit [Fintype Q] in theorem actual_tile_entry (κ : Q → Physical a b S) (i : Fin a) {t : ℤ}
    (htM : t∈grid a) (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hp : 0<p) (hnil : (2:R)^p=0) (z : R)
    (w : Physical a b S) (τ : Fin (2^(i.val+1)))
    (hbit : w.2.val.testBit i.val=τ.val.testBit i.val) (q : Q)
    (hq : tile i.val (κ q).2.val=τ.val) :
    (W a t (((κ q).2.val:ℤ)-(w.2.val:ℤ))).eval₂ (J6ZeroTransport.reduceAt p hnil) z =
      ∑ c ∈ Finset.range (p-1),
        mode a p hnil i.isLt.le (crossingOf ht hv hbit) z c * (coord i.val (κ q).2.val:R)^c := by
  have hseat := (tile_coordinates i.val (κ q).2.val).2
  rw [hq] at hseat
  have he : k i.val w.2.val τ.val (coord i.val (κ q).2.val) =
      ((κ q).2.val:ℤ)-(w.2.val:ℤ) := by
    have hh := congrArg (fun n : ℕ => (n:ℤ)) hseat
    push_cast at hh
    unfold k
    rw [←hh]
  have hmem : k i.val w.2.val τ.val (coord i.val (κ q).2.val)∈grid a := by
    rw [he]
    exact difference_mem_grid w.2 (κ q).2
  simpa only [he] using actual_W_receives (coord i.val (κ q).2.val) htM hmem i.isLt.le
    (crossingOf ht hv hbit) p hp hnil z

theorem actual_tile_value (κ : Q → Physical a b S) (i : Fin a) {t : ℤ}
    (htM : t∈grid a) (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hp : 0<p) (hnil : (2:R)^p=0) (z : R)
    (w : Physical a b S) (τ : Fin (2^(i.val+1)))
    (hbit : w.2.val.testBit i.val=τ.val.testBit i.val) (X : Q → Bool)
    [DecidableEq (Page a b S)] :
    (∑ q ∈ columns (fun q => (κ q).1) (fun q => (κ q).2.val) i.val w.1 τ.val,
      (W a t (((κ q).2.val:ℤ)-(w.2.val:ℤ))).eval₂ (J6ZeroTransport.reduceAt p hnil) z *
        bit R (X q)) =
    ∑ c ∈ Finset.range (p-1),
      mode a p hnil i.isLt.le (crossingOf ht hv hbit) z c *
        L (fun q => (κ q).1) (fun q => (κ q).2.val) i.val w.1 τ.val c X := by
  rw [← regroup_modes]
  refine Finset.sum_congr rfl (fun q hq => ?_)
  have htile := (Finset.mem_filter.mp hq).2.2
  rw [actual_tile_entry κ i htM ht hv p hp hnil z w τ hbit q htile]

#print axioms difference_mem_grid
#print axioms actual_tile_entry
#print axioms actual_tile_value
end J6R9PacketRealTile
