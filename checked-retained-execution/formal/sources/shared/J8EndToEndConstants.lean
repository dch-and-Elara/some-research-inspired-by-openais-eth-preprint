import J8EndToEndPhysical

/-!
The printed low-order kernels at the physical layout: the base constant
reads the uniquely matched old-column input, and the normalized crossing
constant is an explicit odd-denominator fraction. Any higher polynomial
tails can be substituted; no assumption on a whole probe vector is made.
-/

namespace J8EndToEnd

open scoped Polynomial BigOperators Classical
open Polynomial DyadicProbeCompiler J8Physical

noncomputable section

variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

/-- Add any supplied true higher terms after the exact local Cauchy
constant. The weight here is the original mesh amplitude in ℤ. -/
def physicalBase (e : EndpointSeating d) (even : Even L) (c : ℤ)
    (tail : IntegralArguments d) : IntegralArguments d :=
  fun g x r leg =>
    C (((localHit d e even r).map fun p =>
        if p.1 = leg then (c : Source) * sourceBit (x.2 p.2.1 p.2.2) else 0).getD 0) +
      X * tail g x r leg

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [DecidableEq V] [Fintype G] [DecidableEq Packet] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem constructed_base_agrees (e : EndpointSeating d) (even : Even L) (c : ℤ)
    (hc : (c : ℚ) = outerAmplitude L) (F : OldTables d) (tail : IntegralArguments d) :
    ArgsAgree d e even F (physicalBase d e even c tail) := by
  intro g x r leg
  simp only [physicalBase, Polynomial.coeff_add, Polynomial.coeff_C_zero,
    Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, add_zero]
  cases hh : localHit d e even r with
  | none =>
    simp only [Option.map_none, Option.getD_none, map_zero, localChild,
      J8SourceMoment.input0, J8SourceMoment.literalChild, groupWiring,
      wiringOfOption_read_none _ _ hh]
  | some v =>
    simp only [Option.map_some, Option.getD_some, localChild,
      J8SourceMoment.input0, J8SourceMoment.literalChild, groupWiring,
      wiringOfOption_read_some _ _ _ _ hh]
    by_cases eq : v.1 = leg
    · simp only [if_pos eq, map_mul, map_intCast, hc, sourceBit_agreement]
      rfl
    · simp only [if_neg eq, map_zero]

def integerDenominator (a : S) (j : TargetPorts d a) : ℤ :=
  (L:ℤ) - 1 - ((d.seat (pinWire d a)).2.val % 2 : ℕ) + (d.seat (j.1.1,j.2)).2.val

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [DecidableEq Packet] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem denominator_cast (a : S) (j : TargetPorts d a) :
    (integerDenominator d a j : ℚ) = physicalDenominator d a j := rfl

def denominatorUnit (a : S) (even : Even L) (hL : 2 < L)
    (b : ℕ) (j : TargetPorts d a) (hj : j ∈ groupedTargets d a) :
    odds :=
  ⟨(integerDenominator d a j)^(b+1),
    (groupedTargets_denom d a even hL hj).2.pow⟩

/-- Actual normalized target constant in the 2-local ring, represented
by a single odd-denominator quotient. Non-target positions have zero
coefficient and no denominator is read there. -/
def physicalKernel (a : S) (even : Even L) (hL : 2 < L) (c : ℤ) (b : ℕ)
    (tail : TargetPorts d a → Source[X]) (j : TargetPorts d a) : Source[X] :=
  if hj : j ∈ groupedTargets d a then
    C (IsLocalization.mk' Source c (denominatorUnit d a even hL b j hj)) + X * tail j
  else 0

omit [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] [Fintype G] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem constructed_kernel_normalized (a : S) (even : Even L) (hL : 2 < L)
    (c : ℤ) (b : ℕ) (tail : TargetPorts d a → Source[X])
    (j : TargetPorts d a) (hj : j ∈ groupedTargets d a) :
    rationalMap ((physicalKernel d a even hL c b tail j).coeff 0) =
      (c : ℚ) / (physicalDenominator d a j)^(b+1) := by
  simp only [physicalKernel, dif_pos hj, Polynomial.coeff_add, Polynomial.coeff_C_zero,
    Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, add_zero]
  apply (eq_div_iff (pow_ne_zero _ (physicalDenominator_pos d a even hL j hj).ne')).mpr
  have h := rationalMap_fraction c (denominatorUnit d a even hL b j hj)
  simpa only [denominatorUnit, Int.cast_pow, denominator_cast] using h

omit [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] [Fintype G] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem constructed_kernel_scales (a : S) (even : Even L) (hL : 2 < L)
    (c : ℤ) (hc : (c:ℚ) = outerAmplitude L) (k : ℕ) (length : L = 2^k)
    (b : ℕ) (tail : TargetPorts d a → Source[X])
    (j : TargetPorts d a) (hj : j ∈ groupedTargets d a) :
    (2:ℚ)^(k+1+b) * rationalMap ((physicalKernel d a even hL c b tail j).coeff 0) =
      J8SourceMoment.exactSlope (outerAmplitude L) (2*(L:ℚ)) (physicalDenominator d a j) b := by
  rw [constructed_kernel_normalized d a even hL c b tail j hj, hc, J8SourceMoment.exactSlope,
    mul_div_assoc, pow_add (2:ℚ) (k+1) b, pow_succ (2:ℚ) k]
  have hcast : (L:ℚ) = (2:ℚ)^k := by exact_mod_cast length
  rw [hcast]
  ring

#print axioms constructed_base_agrees
#print axioms constructed_kernel_normalized
#print axioms constructed_kernel_scales

end
end J8EndToEnd
