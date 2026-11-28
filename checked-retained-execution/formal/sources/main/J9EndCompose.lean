import J9EndProbe
import J8EndToEnd

/-! J9 readout with native printed precision, real packet seating and
actual slot addresses. The only coefficient-facing interface is an
exact identity over Q; no finite congruence is externally furnished. -/

namespace J9End
open scoped BigOperators Polynomial Classical
open Polynomial NativeProbeRing DyadicProbeCompiler

noncomputable section
variable {Packet R S V G A K : Type*} {P : V → Type*}
variable [Fintype R] [DecidableEq R] [Fintype Packet] [DecidableEq Packet] [DecidableEq G]
variable [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]

theorem recover_physical_printed_from_high_samples
    (s M nativeP b : ℕ)
    (d : J8Physical.Layout Packet R S V G P (J9PrintedSchedule.rootL (Nat.clog 2 s)))
    (seat : J8Physical.EndpointSeating d) (anchor : S) (idx : J8Physical.Wire R ≃ Fin M)
    (tables : LiteralPortCompiler.CNF (Fin M))
    (hLambda : 262144 ≤ Nat.clog 2 s)
    (hActive : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M)
    (hP : 0 < nativeP) (hb : b < J9PrintedSchedule.rootL (Nat.clog 2 s))
    (capacity : J9PrintedSchedule.rootL (Nat.clog 2 s) * Fintype.card Packet ≤ 3*M)
    (rows : (Fin M → Bool) → R → Bool → ℚ[X])
    (cross : Fin (J9PrintedSchedule.rootL (Nat.clog 2 s)) → ℚ[X])
    (source : (Fin M → Bool) → ℚ[X])
    (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree) [Fact (Irreducible (residuePoly f))]
    (fit : 10*M+1 ≤ 2^f.natDegree)
    (F : LiteralPortCompiler.CNF A) (base : (A → Bool) → A → Source[X])
    (kernel : (A → Bool) → A → K → Source[X]) (weight : K → ℕ) (m : K) (hv : 1 ≤ weight m)
    (exactFirst :
      (2 : ℚ)^weight m * J8EndToEnd.rationalMap
        ((MvPolynomial.coeff (Finsupp.single m 1) (LiteralPortCompiler.completed F base kernel)).coeff 0)
      = (literalCompleted (chart d anchor idx (LiteralPortCompiler.satisfied tables)) b rows cross source).coeff 1) :
    let lambda := Nat.clog 2 s
    let L := J9PrintedSchedule.rootL lambda
    let u := J9PrintedSchedule.rootU lambda
    let a := J9PrintedSchedule.rootA lambda
    let q := J9PrintedSchedule.precision nativeP ((3*M+u-1)/u) L M a
    let p := 10*M
    have hA : 1 ≤ a := by
      change 1 ≤ J9PrintedSchedule.rootA lambda
      unfold J9PrintedSchedule.rootA
      have ht := (J9PrintedSchedule.rootL_ge_six_iff_u lambda).1
        ((J9PrintedSchedule.rootL_ge_six_iff_lambda lambda).2 hLambda)
      omega
    have hpq : p ≤ q := (J9PrintedSchedule.precision_gt_ten _ _ _ _ _ hP hA).le
    let g := chart d anchor idx (LiteralPortCompiler.satisfied tables)
    let x := fun i => probe p f (chosenRep f.natDegree (p+1) fit i)
    let obs := fun i => reduceScalar p q hpq f
      (observation q f (chosenRep f.natDegree (p+1) fit i) F base kernel weight m)
    10*M+1 ≤ J9PrintedSchedule.probeCount M L ∧
      ((projectBase p f hf ((J9FactorBounds.publicDenominator g b : Scalar p f) *
        NativeInterpolation.decode x obs ⟨1, by omega⟩)).valMinAbs : ℚ) /
        J9FactorBounds.publicDenominator g b = (literalCompleted g b rows cross source).coeff 1 := by
  dsimp only
  let lambda := Nat.clog 2 s
  let L := J9PrintedSchedule.rootL lambda
  let u := J9PrintedSchedule.rootU lambda
  let a := J9PrintedSchedule.rootA lambda
  let q := J9PrintedSchedule.precision nativeP ((3*M+u-1)/u) L M a
  have hA : 1 ≤ a := by
      change 1 ≤ J9PrintedSchedule.rootA lambda
      unfold J9PrintedSchedule.rootA
      have ht := (J9PrintedSchedule.rootL_ge_six_iff_u lambda).1
        ((J9PrintedSchedule.rootL_ge_six_iff_lambda lambda).2 hLambda)
      omega
  have hpq : 10*M ≤ q := (J9PrintedSchedule.precision_gt_ten _ _ _ _ _ hP hA).le
  let truth := LiteralPortCompiler.satisfied tables
  let g := chart d anchor idx truth
  have hL : 6 ≤ L := (J9PrintedSchedule.rootL_ge_six_iff_lambda lambda).2 hLambda
  have hsmall : 3 ≤ L := by omega
  have hu : 1 ≤ u := by
    have ht := (J9PrintedSchedule.rootL_ge_six_iff_u lambda).1 hL
    change 2 ≤ u at ht
    omega
  have heven : L % 2 = 0 := by
    have ho := J9PrintedSchedule.root_outer_odd lambda hu
    change (L-1)%2=1 at ho
    omega
  have hcube : L^3 ≤ M := J9PrintedSchedule.root_cube_le_active_M s M hActive
  have hpar : ∀ i ∈ g.targets, i.val%2 = g.tau.val%2 := by
    intro i hi
    rw [Nat.mod_eq_of_lt g.tau.isLt]
    exact chart_parity d anchor idx truth i hi
  have hfirst := literal_first_exact g b rows cross source
  have hnum := (J9FactorBounds.cleared_exact_odd g b hsmall heven hpar).2
  rw [← hfirst, ← exactFirst] at hnum
  have hexact :
      algebraMap ℤ Source (J9FactorBounds.publicDenominator g b) *
        (2 : Source)^weight m *
        (MvPolynomial.coeff (Finsupp.single m 1) (LiteralPortCompiler.completed F base kernel)).coeff 0 =
      algebraMap ℤ Source (J9FactorBounds.exactCleared g b) := by
    apply J8EndToEnd.rationalMap_injective
    have hr (n : ℤ) : J8EndToEnd.rationalMap (algebraMap ℤ Source n) = (n : ℚ) :=
      IsLocalization.lift_eq J8EndToEnd.oddRatUnit n
    simpa only [hr,map_mul,map_pow,map_ofNat,mul_assoc] using hnum.symm
  exact ⟨J9PrintedSchedule.probes_ge_ten_add_one _ _ hL,
    recover_literal_first_from_high_samples g b hsmall heven hb hcube hpar
      (chart_tile_injective d anchor idx truth) (chart_one_hit d anchor idx truth seat)
      (chart_active_rows_budget d anchor idx truth capacity) rows cross source
      q hpq f hf hd fit F base kernel weight m hv hexact⟩

#print axioms recover_physical_printed_from_high_samples

end
end J9End

