import J6NativeHeightKernel
import P1DyadicGridBridge
import Mathlib.Tactic

/-! The actual Appendix D coordinate-zero grouping on the J6 odd
mesh. The row and column orientations are opposite, as in the
printed template. Every surviving shift is local; all targeted
crossing coefficients at zeta = 0 have nonzero denominators and vanish. -/
namespace J6RecursiveCrossing
open P1DyadicGrid P1DyadicGridBridge J6Mesh
open J6PhysicalPacking J6NativeHeightPort
open scoped BigOperators

theorem odd_center_valuation (m : ℕ) (i : Fin (m+1)) :
    (index m i : ℤ) ≠ 0 ∧ padicValInt 2 (index m i : ℤ) = 0 ∧
      (index m i : ℤ) ∈ grid (a m) := by
  have hT : 0 < (index m i : ℤ) := by exact_mod_cast (address_index m i).1
  obtain ⟨k,hk⟩ := (address_index m i).2.1
  have ho : Odd (index m i : ℤ) := ⟨(k:ℤ),by exact_mod_cast hk⟩
  have hL : (index m i : ℤ) < pow₂ (a m) := by
    unfold pow₂
    exact_mod_cast (address_index m i).2.2.2
  have hp := pow₂_pos (a m)
  exact ⟨hT.ne',odd_valuation_zero ho,mem_grid.mpr ⟨by omega,hL⟩⟩

def rowLabel {S : Type*} (lo hi : S) (x : ℕ) : S :=
  if x.testBit 0 then hi else lo

def colLabel {S : Type*} (lo hi : S) (y : ℕ) : S :=
  if y.testBit 0 then lo else hi

theorem shift_same_group {S : Type*} (lo hi : S) (m : ℕ) (i : Fin (m+1)) (x y : ℕ)
    (h : x+index m i=y) : rowLabel lo hi x = colLabel lo hi y := by
  obtain ⟨ht,hv,_⟩ := odd_center_valuation m i
  have hd : (y:ℤ)-(x:ℤ)=(index m i:ℤ) := by omega
  have hb := shifted_bit_flip ht hv hd
  unfold rowLabel colLabel
  cases hp : x.testBit 0 <;> simp [hp,hb]

theorem crossing_same_bit {S : Type*} (lo hi : S) (x τ : ℕ)
    (h : rowLabel lo hi x ≠ colLabel lo hi τ) : x.testBit 0=τ.testBit 0 := by
  cases hx : x.testBit 0 <;> cases hy : τ.testBit 0 <;>
    simp [rowLabel,colLabel,hx,hy] at h ⊢

theorem literal_crossing_zero {S : Type*} (lo hi : S)
    (m : ℕ) (i : Fin (m+1)) (x τ b : ℕ) (h : rowLabel lo hi x ≠ colLabel lo hi τ) :
    crossingInt (index m i) x τ ≠ 0 ∧
      printedCoefficient (F:=ℚ) (a m) 0 b (index m i) x τ 0 = 0 := by
  obtain ⟨hn,hv,ht⟩ := odd_center_valuation m i
  have hbit := crossing_same_bit lo hi x τ h
  refine ⟨(crossing_nonzero_and_le hn hv hbit).1,?_⟩
  unfold printedCoefficient
  simp only [mul_zero,add_zero,sourceNumerator]
  rw [Finset.prod_eq_zero ht (by simp),zero_div,zero_mul]

/-- Apply locality to the immutable J6 packet subscript, with the two
coordinate-zero symbols of the occupied template. -/
theorem packed_shift_local {C S : Type*} [DecidableEq C] (first second : C → S)
    (rho : C) (m l : ℕ) (h : m ≤ K m) (i : Fin (m+1))
    (p q : Wire rho m (K m) l)
    (hq : shiftedWire rho m (K m) l h (index m i) p = some q) :
    let s := place rho m (K m) l h p
    let r := place rho m (K m) l h q
    rowLabel (first s.1) (second s.1) s.2.2.val =
      colLabel (first r.1) (second r.1) r.2.2.val := by
  obtain ⟨hc,_,hidx⟩ := (shifted_iff_reaches _ _ _ _ _ _ _ _).mp hq
  dsimp only
  rw [← hc]
  exact shift_same_group _ _ m i _ _ hidx

#print axioms odd_center_valuation
#print axioms shift_same_group
#print axioms literal_crossing_zero
#print axioms packed_shift_local
end J6RecursiveCrossing
