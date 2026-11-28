import J9LayoutTransferPhysical
import J8EndToEnd

/-! The same singleton is built over the native odd-denominator
localization, before any finite-ring reduction. -/
namespace J9LayoutTransfer
open scoped BigOperators Classical Polynomial
open LiteralPortCompiler DyadicProbeCompiler

noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L M : ℕ}
variable [Fintype R] [DecidableEq R] [Fintype Packet] [DecidableEq Packet] [DecidableEq G]
variable (d : J8Physical.Layout Packet R S V G P L)

def localizedBase (anchor : S) (idx : Port R ≃ Fin M) (truth : (Fin M → Bool) → Bool)
    (x : Fin M → Bool) (p : Port R) : Source :=
  let g := J9End.chart d anchor idx truth
  (J9FactorBounds.arg (J9FactorBounds.kernel L) (g.hit p.1 p.2) (x (g.rowInput p.1 p.2)) : ℤ)

def localizedKernel (anchor : S) (idx : Port R ≃ Fin M) (truth : (Fin M → Bool) → Bool)
    (b : ℕ) (hL : 3 ≤ L) (hEven : L % 2 = 0) (p : Port R) : Source :=
  let g := J9End.chart d anchor idx truth
  if hp : p ∈ J8Physical.targets d (J8Physical.pinWire d anchor) then
    let i := J9End.slot d p
    have hi : i ∈ g.targets := Finset.mem_image.mpr ⟨p,hp,rfl⟩
    have hpar : ∀ j ∈ g.targets, j.val%2 = g.tau.val%2 := by
      intro j hj
      rw [Nat.mod_eq_of_lt g.tau.isLt]
      exact J9End.chart_parity d anchor idx truth j hj
    IsLocalization.mk' (M := odds) Source (J9FactorBounds.kernel L)
      ⟨J9FactorBounds.denominator g b i,
        (J9FactorBounds.local_den_positive_odd g b hL hEven hpar i hi).2⟩
  else 0

omit [Fintype Packet] in
theorem localizedKernel_map (anchor : S) (idx : Port R ≃ Fin M)
    (truth : (Fin M → Bool) → Bool) (b : ℕ) (hL : 3 ≤ L) (hEven : L % 2 = 0)
    (p : Port R) :
    J8EndToEnd.rationalMap (localizedKernel d anchor idx truth b hL hEven p) =
      chartKernel d anchor idx truth b p := by
  unfold localizedKernel chartKernel
  dsimp only
  split <;> rename_i hp
  · exact (eq_div_iff ((J8EndToEnd.oddRatUnit _).ne_zero)).mpr
      (J8EndToEnd.rationalMap_fraction _ _)
  · exact map_zero _

/-- Exact normalized slot: same original column labels, literal compiler
on the original binary row labels, and normalized odd Cauchy kernels. -/
def localizedSlot (anchor : S) (idx : Port R ≃ Fin M) (truth : (Fin M → Bool) → Bool)
    (b : ℕ) (hL : 3 ≤ L) (hEven : L % 2 = 0) : Source :=
  let g := J9End.chart d anchor idx truth
  ∑ x : Fin M → Bool, (if g.table x then 1 else 0) *
    (J9FactorBounds.moment g b x : Source) *
    MvPolynomial.coeff β
      (rowCompiler (localizedBase d anchor idx truth x)
        (localizedKernel d anchor idx truth b hL hEven))

omit [Fintype Packet] in
theorem localizedSlot_map (anchor : S) (idx : Port R ≃ Fin M)
    (truth : (Fin M → Bool) → Bool) (b : ℕ) (hL : 3 ≤ L) (hEven : L % 2 = 0) :
    let g := J9End.chart d anchor idx truth
    J8EndToEnd.rationalMap (localizedSlot d anchor idx truth b hL hEven) =
      ∑ x : Fin M → Bool, chartWeight g b x *
        MvPolynomial.coeff β (rowCompiler (chartBase g x) (chartKernel d anchor idx truth b)) := by
  dsimp only
  rw [localizedSlot, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [map_mul, map_mul, map_intCast]
  have hc :
      J8EndToEnd.rationalMap (MvPolynomial.coeff β
        (rowCompiler (localizedBase d anchor idx truth x)
          (localizedKernel d anchor idx truth b hL hEven))) =
      MvPolynomial.coeff β (rowCompiler (chartBase (J9End.chart d anchor idx truth) x)
        (chartKernel d anchor idx truth b)) := by
    simp only [rowCompiler, reduce_completed,
      localizedKernel_map d anchor idx truth b hL hEven, localizedBase, chartBase, map_intCast]
  rw [hc]
  unfold chartWeight
  cases h : (J9End.chart d anchor idx truth).table x <;> simp

/-- The exact coefficient link over Q for this explicit native
literal-row slot, with the printed singleton exponent a+1+b. -/
theorem localizedSlot_signed_first (anchor : S) (idx : Port R ≃ Fin M)
    (truth : (Fin M → Bool) → Bool) (b a : ℕ) (hPow : L = 2^a) (hL : 3 ≤ L) (hEven : L % 2 = 0)
    (rows : (Fin M → Bool) → R → Bool → ℚ[X]) (cross : Fin L → ℚ[X])
    (source : (Fin M → Bool) → ℚ[X]) :
    (2 : ℚ)^(a+1+b) * J8EndToEnd.rationalMap (localizedSlot d anchor idx truth b hL hEven) =
      (J9End.literalCompleted (J9End.chart d anchor idx truth) b rows cross source).coeff 1 := by
  rw [localizedSlot_map, J9End.literal_first_exact]
  have hLQ : (L:ℚ) = 2^a := by exact_mod_cast hPow
  have hh : ((2:ℚ)*(L:ℚ)*2^b) = 2^(a+1+b) := by rw [hLQ,pow_add,pow_add]; ring
  rw [← hh]
  exact normalized_rows_full_cube d anchor idx truth b

#print axioms localizedKernel_map
#print axioms localizedSlot_map
#print axioms localizedSlot_signed_first
end
end J9LayoutTransfer

