import J8PhysicalWiring
import Mathlib.Data.Int.Interval

/-!
Agreement of the actual Appendix D Cauchy entries at the extreme node with
the physical child readout. The square-free grid factors are not replaced
by an assumed partial shift.
-/

namespace J8Physical

open scoped BigOperators Classical

noncomputable section

def printedGrid (L : ℕ) : Finset ℤ := Finset.Ico (-(L:ℤ)) (L:ℤ)

def derivativeProduct (L : ℕ) (t : ℤ) : ℚ :=
  ∏ j ∈ (printedGrid L).erase t, ((t-j : ℤ) : ℚ)

def outerAmplitude (L : ℕ) : ℚ := derivativeProduct L ((L:ℤ)-1) / derivativeProduct L 0

theorem amplitude_negative (L : ℕ) (hL : 0 < L) (even : Even L) : outerAmplitude L < 0 := by
  classical
  have htop : 0 < derivativeProduct L ((L:ℤ)-1) := by
    apply Finset.prod_pos
    intro j hj
    obtain ⟨hne, hjs⟩ := Finset.mem_erase.mp hj
    have h := (Finset.mem_Ico.mp hjs).2
    exact_mod_cast (show (0:ℤ) < (L:ℤ)-1-j by omega)
  let neg : Finset ℤ := Finset.Icc (-(L:ℤ)) (-1)
  let pos : Finset ℤ := Finset.Icc 1 ((L:ℤ)-1)
  have dis : Disjoint neg pos := by
    rw [Finset.disjoint_left]
    intro j hn hp
    simp only [neg, pos, Finset.mem_Icc] at hn hp
    omega
  have partition : (printedGrid L).erase 0 = neg ∪ pos := by
    ext j
    simp only [printedGrid, Finset.mem_erase, Finset.mem_Ico, Finset.mem_union,
      neg, pos, Finset.mem_Icc]
    omega
  have hnegpos : 0 < ∏ j ∈ neg, ((-j : ℤ) : ℚ) := by
    apply Finset.prod_pos
    intro j hj
    have hn := (Finset.mem_Icc.mp hj).2
    exact_mod_cast (show (0:ℤ) < -j by omega)
  have hpospos : 0 < ∏ j ∈ pos, (j : ℚ) := by
    apply Finset.prod_pos
    intro j hj
    have hp := (Finset.mem_Icc.mp hj).1
    exact_mod_cast (show (0:ℤ) < j by omega)
  have hposcard : pos.card = 2*(L/2-1)+1 := by
    obtain ⟨k,hk⟩ := even
    unfold pos
    rw [Int.card_Icc]
    omega
  have hsign : (-1:ℚ)^pos.card = -1 := by
    rw [hposcard, pow_add, pow_mul]
    norm_num
  have hposneg : (∏ j ∈ pos, ((-j : ℤ) : ℚ)) < 0 := by
    have f : (fun j : ℤ => ((-j : ℤ) : ℚ)) = fun j : ℤ => (-1:ℚ)*(j:ℚ) := by
      funext j
      simp
    rw [f, Finset.prod_mul_distrib, Finset.prod_const, hsign, neg_one_mul]
    exact neg_neg_of_pos hpospos
  have hden : derivativeProduct L 0 < 0 := by
    unfold derivativeProduct
    rw [partition, Finset.prod_union dis]
    simp only [zero_sub]
    exact mul_neg_of_pos_of_neg hnegpos hposneg
  exact div_neg_of_pos_of_neg htop hden

variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [DecidableEq Packet]

/-- Literal rational polynomial quotient at t=L-1, before any reduction. -/
def centerKernel (x y : Wire R) : ℚ :=
  if (d.seat x).1 = (d.seat y).1 then
    (∏ j ∈ (printedGrid L).erase ((d.seat y).2.val - (d.seat x).2.val : ℤ),
      ((((L:ℤ)-1)-j : ℤ) : ℚ)) / derivativeProduct L 0
  else 0

theorem centerKernel_exact (x y : Wire R) :
    centerKernel d x y = if Shift d x y then outerAmplitude L else 0 := by
  have hL : 0 < L := (d.seat y).2.isLt.pos
  have ht : ((L:ℤ)-1) ∈ printedGrid L := by
    simp only [printedGrid, Finset.mem_Ico]
    omega
  by_cases h : Shift d x y
  · have hΔ : ((d.seat y).2.val : ℤ) - (d.seat x).2.val = (L:ℤ)-1 := by
      have he := h.2
      omega
    simp only [centerKernel, if_pos h.1, if_pos h, hΔ, outerAmplitude, derivativeProduct]
  · rw [if_neg h, centerKernel]
    split_ifs with hs
    · have hΔ : ((L:ℤ)-1) ≠ ((d.seat y).2.val : ℤ) - (d.seat x).2.val := by
        intro e
        exact h ⟨hs, by omega⟩
      have hz := Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨hΔ, ht⟩)
        (f := fun j : ℤ => ((((L:ℤ)-1)-j : ℤ) : ℚ)) (by simp)
      rw [hz, zero_div]
    · rfl

variable [Fintype R]

def physicalArgument (X : Wire R → Bool) (x : Wire R) : ℚ :=
  ∑ y : Wire R, centerKernel d x y * NativeChildRealization.bitValue ℚ (X y)

theorem physicalArgument_hit (X : Wire R → Bool) {x y : Wire R}
    (h : Shift d x y) :
    physicalArgument d X x = outerAmplitude L * NativeChildRealization.bitValue ℚ (X y) := by
  classical
  unfold physicalArgument
  rw [Finset.sum_eq_single_of_mem y (Finset.mem_univ y)]
  · simp [centerKernel_exact, h]
  · intro z _ hz
    have hn : ¬ Shift d x z := fun hs => hz (successor_unique d hs h)
    simp [centerKernel_exact, hn]

theorem physicalArgument_no_hit (X : Wire R → Bool) (x : Wire R)
    (h : ∀ y, ¬ Shift d x y) : physicalArgument d X x = 0 := by
  apply Finset.sum_eq_zero
  intro y _
  simp [centerKernel_exact, h y]

/-- The whole baseline argument is independent of all unary pin signs:
a surviving physical column is provably nonpin, not merely assumed
to have a public bit. -/
theorem physicalArgument_pin_invariant (e : EndpointSeating d)
    (X Y : Wire R → Bool) (x : Wire R)
    (agree : ∀ y (p : Sigma P), d.column y = Sum.inr p → X y = Y y) :
    physicalArgument d X x = physicalArgument d Y x := by
  by_cases h : ∃ y, Shift d x y
  · obtain ⟨y,hy⟩ := h
    obtain ⟨p,hp⟩ := hit_is_nonpin d e hy
    rw [physicalArgument_hit d X hy, physicalArgument_hit d Y hy, agree y p hp]
  · rw [physicalArgument_no_hit d X x (not_exists.mp h),
      physicalArgument_no_hit d Y x (not_exists.mp h)]

section KernelTransfer

variable [DecidableEq R] [Fintype V] [DecidableEq V] [DecidableEq G]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

def localBitsFromWire (g : G) (X : Wire R → Bool)
    (v : LocalColumn d g) (p : LocalPort d v) : Bool :=
  X (recoverWire d ⟨v,p⟩)

omit [DecidableEq R] [DecidableEq V] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
/-- Pass the actual original Cauchy center argument to the existing J8
source/target compiler. No equality of abstract hit functions is an
assumption. Even the old-column assignment is a concrete restriction
of the same original physical port assignment. -/
theorem center_to_compiled_argument (e : EndpointSeating d) (even : Even L) {g : G}
    (F : (v : LocalColumn d g) → LiteralPortCompiler.CNF (LocalPort d v))
    (X : Wire R → Bool) (r : LocalRow d g) (b : Bool) :
    physicalArgument d X (r.1,b) =
      J8SourceMoment.input0
        (J8SourceMoment.literalChild (groupWiring d e even g) (outerAmplitude L) F)
        (localBitsFromWire d g X) r b := by
  cases hh : localHit d e even r with
  | none =>
    have nh : ∀ y, ¬ Shift d (r.1,b) y := by
      intro y hy
      have h := localHit_complete d e even r hy
      rw [hh] at h
      cases h
    rw [physicalArgument_no_hit d X _ nh]
    simp only [J8SourceMoment.input0, J8SourceMoment.literalChild, groupWiring,
      wiringOfOption_read_none _ _ hh]
  | some addr =>
    have good := localHit_sound d e even r hh
    simp only [J8SourceMoment.input0, J8SourceMoment.literalChild, groupWiring,
      wiringOfOption_read_some _ _ _ _ hh]
    by_cases hb : addr.1 = b
    · have hb' : Shift d (r.1,b) (recoverWire d addr.2) := by simpa only [hb] using good
      rw [physicalArgument_hit d X hb', if_pos hb]
      rfl
    · have nh : ∀ y, ¬ Shift d (r.1,b) y := by
        intro y hy
        exact hb (congrArg Prod.snd (row_hit_unique d e good hy rfl))
      rw [physicalArgument_no_hit d X _ nh, if_neg hb]

end KernelTransfer


#print axioms amplitude_negative
#print axioms centerKernel_exact
#print axioms physicalArgument_hit
#print axioms physicalArgument_no_hit
#print axioms physicalArgument_pin_invariant
#print axioms center_to_compiled_argument

end
end J8Physical
