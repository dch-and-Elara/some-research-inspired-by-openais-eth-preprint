import J7PrintedParamsSchedule
import Mathlib.Data.Nat.Sqrt

/-! # Original non-leaf root and packet budget on the four-clone count input. -/
open scoped BigOperators Classical

namespace J7PrintedParams
open J7SourceLabels J7FullWordCells J7FullWordAssembly J7SeatSource
open J7SeatPacking J7SeatRounded P11FullPacking J7ToJ8Incidence J7ToJ8Layout

noncomputable section
set_option maxHeartbeats 1800000

def leafThreshold (s : ℕ) : ℕ := Nat.ceil ((s:ℚ)/Nat.sqrt (Nat.clog 2 s))

theorem root_active (s M : ℕ) (hs : 3 ≤ s) (hM : s ≤ M)
    (hlog : 4 ≤ Nat.clog 2 s) : leafThreshold s < M := by
  have h2 := (Nat.le_sqrt.2 hlog : 2 ≤ Nat.sqrt (Nat.clog 2 s))
  have h2q : (2:ℚ) ≤ (Nat.sqrt (Nat.clog 2 s):ℕ) := by exact_mod_cast h2
  have hpos : (0:ℚ) < (Nat.sqrt (Nat.clog 2 s):ℕ) := by linarith
  have hq : (s:ℚ) ≤ ((s-1:ℕ):ℚ) * 2 := by
    rw [Nat.cast_sub (by omega : 1 ≤ s),Nat.cast_one]
    have hs' : (3:ℚ) ≤ s := by exact_mod_cast hs
    linarith
  have hc : leafThreshold s ≤ s-1 :=
    Nat.ceil_le.2 ((div_le_iff₀ hpos).2 (hq.trans (mul_le_mul_of_nonneg_left h2q (by positivity))))
  omega

theorem four_clone_root_active (N : ℕ) (he : N%2=0)
    (large : 2^(9*131072-1) < sourceSize N) :
    leafThreshold (sourceSize N) < 24*N := by
  refine root_active _ _ ?_ (source_size N he).2 ?_
  · have hu := u_large _ large
    unfold rootU at hu
    have hlog : 1 < Nat.clog 2 (sourceSize N) := by omega
    have hb : (2:ℕ)^1 < sourceSize N := (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).1 hlog
    exact hb
  · have hu := u_large _ large
    unfold rootU at hu
    omega

variable {A Pair Row Col W : Type*} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W]

/-- The actual root parameters from the paper, not externally supplied
packing inequalities or matching degree, yield the native J7/J8 layout.
The source's graph and its exact incidence counts remain input data. -/
theorem four_clone_native_root
    (hA : Fintype.card A = 64) (N : ℕ) (he : N%2=0)
    (large : 2^(9*131072-1) < sourceSize N)
    (hN : Fintype.card (Pin Pair) = N) (hM : Fintype.card (Wire Pair W) = 24*N)
    (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (row_two : ∀ r, Nat.card {w : W // row w = r} = 2)
    (clone_cap : ∀ p : Pin Pair, (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 2)
    (col_cap : ∀ c, (Finset.univ.filter fun w : W => col w = Sum.inr c).card ≤ 3)
    (reference : State A (Fin (rootT (sourceSize N)) → A) Pair Row Col)
    (ref : Seed A (Fin (rootT (sourceSize N)) → A)) :
    let t := rootT (sourceSize N)
    leafThreshold (sourceSize N) < 24*N ∧
    ∃ z : State A (Fin t → A) Pair Row Col,
      let b' := ceilCopies (2^(t+1)) (realMaximum (wordLabel row col z))
      Nat.card (Page (t+1) b' A)*printedL t ≤ 3*(24*N) ∧
      ∃ j : Wire Pair W ↪ Physical (t+1) b' A,
      ∃ preserve : ∀ w, physicalCell (balancedMask (t+1) b') (j w) = wordLabel row col z w,
      (∀ s, isEnd s → ∃ w, j w = s) ∧
      let layout := physicalLayout row col row_two z j preserve
      Nonempty (J8Physical.EndpointSeating layout) ∧
      (∀ p (x : J8Physical.Wire (Subdivision Pair Row)),
        ¬ J8Physical.Shift layout x (J8Physical.pinWire layout p)) ∧
      (∀ x y, J8Physical.Shift layout x y → layout.rowLabel x.1 = J8Physical.actualColLabel layout y) ∧
      (∀ p, (J8Physical.targets layout (J8Physical.pinWire layout p)).Nonempty) := by
  classical
  dsimp only
  let t := rootT (sourceSize N)
  let D := printedD t
  let L := printedL t
  obtain ⟨hL,p1,p2,p3⟩ := four_clone_root_packing N he large
  obtain ⟨z,hseat,j,hj,hfill,hend,hnop,hchild,htarg⟩ :=
    printed_endpoints hA N (rootDelta (sourceSize N)) hN hM hL p1 p2 p3 row col row_two clone_cap col_cap reference ref
  let b := ceilCopies (2^(t+1)) (realMaximum (wordLabel row col z))
  have hcard : Nat.card (Page (t+1) b A)*L = D*(b*L) := by
    have hc := total_slots (balancedMask (K:=A) (t+1) b)
    rw [total_cells, hA] at hc
    exact hc
  have hD : (0:ℚ) < D := by exact_mod_cast printedD_pos t
  have hbound : (b:ℚ)*L ≤ 3*(24*(N:ℚ))/(D:ℚ) := by
    unfold mu at hseat
    simpa only [mul_div_assoc] using hseat
  have het := (le_div_iff₀ hD).1 hbound
  have hp : Nat.card (Page (t+1) b A)*L ≤ 3*(24*N) := by
    rw [hcard,mul_comm D]
    exact_mod_cast (show (b:ℚ)*L*D ≤ 3*(24*(N:ℚ)) by simpa only [mul_assoc] using het)
  exact ⟨four_clone_root_active N he large, z,hp,j,hj,hfill,hend,hnop,hchild,htarg⟩

#print axioms root_active
#print axioms four_clone_root_active
#print axioms four_clone_native_root

end
end J7PrintedParams
