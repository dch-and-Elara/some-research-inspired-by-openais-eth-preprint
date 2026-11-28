import J6R14SpecializedBoxFactors
import J8PhysicalKernel

/-! Native constant matching and the precise obligation for higher
coefficients. The centre lemma is on the original Cauchy packet
weights and the restriction of the very same wire assignment. If a
literal normalized row/crossing polynomial is available, no unrelated
higher-tail callback is needed: its own divX is the required tail. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial DyadicProbeCompiler J8Physical J8EndToEnd J8J9Grouped

noncomputable section
variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

set_option linter.unusedSectionVars false in
theorem physical_base_at_original_center (e : EndpointSeating d) (even : Even L)
    (F : OldTables d) (tail : IntegralArguments d) (g : G) (X : Wire R→Bool)
    (bits : LocalPin d g→Bool) (r : LocalRow d g) (leg : Bool) :
    rationalMap
      ((physicalBase d e even (J9FactorBounds.kernel L) tail g
        (bits,localBitsFromWire d g X) r leg).coeff 0) =
      physicalArgument d X (r.1,leg) := by
  have hL : 0 < L := (d.seat (r.1,leg)).2.isLt.pos
  have hc := printed_amplitude_integral L (by omega) even
  exact (constructed_base_agrees d e even (J9FactorBounds.kernel L) hc F tail
    g (bits,localBitsFromWire d g X) r leg).trans
      (center_to_compiled_argument d e even (F g) X r leg).symm

set_option linter.unusedSectionVars false in
theorem native_base_realized_by_own_tail (e : EndpointSeating d) (even : Even L)
    (B : IntegralArguments d)
    (h : ∀ g x r leg, (B g x r leg).coeff 0 =
      (physicalBase d e even (J9FactorBounds.kernel L) (fun _ _ _ _ => 0) g x r leg).coeff 0) :
    physicalBase d e even (J9FactorBounds.kernel L)
      (fun g x r leg => (B g x r leg).divX) = B := by
  funext g x r leg
  have h0 := h g x r leg
  simp only [physicalBase,mul_zero,add_zero,coeff_C_zero] at h0
  unfold physicalBase
  rw [← h0,add_comm,X_mul_divX_add]

set_option linter.unusedSectionVars false in
theorem native_crossing_realized_by_own_tail (even : Even L)
    (hL : 2<L) (a : S) (b : ℕ) (K : TargetPorts d a→Source[X])
    (h : ∀ j ∈ groupedTargets d a, (K j).coeff 0 =
      (physicalKernel d a even hL (J9FactorBounds.kernel L) b (fun _ => 0) j).coeff 0)
    (off : ∀ j, j ∉ groupedTargets d a → K j = 0) :
    physicalKernel d a even hL (J9FactorBounds.kernel L) b (fun j => (K j).divX) = K := by
  funext j
  by_cases hj : j ∈ groupedTargets d a
  · have h0 := h j hj
    simp only [physicalKernel,dif_pos hj,mul_zero,add_zero,coeff_C_zero] at h0
    simp only [physicalKernel,dif_pos hj]
    rw [← h0,add_comm,X_mul_divX_add]
  · simpa only [physicalKernel,dif_neg hj] using (off j hj).symm

set_option linter.unusedSectionVars false in
theorem distinct_allowed_tails (e : EndpointSeating d) (even : Even L) (g : G) (x :
    (LocalPin d g→Bool) × LocalBits d g) (r : LocalRow d g) (leg : Bool) :
    physicalBase d e even (J9FactorBounds.kernel L) (fun _ _ _ _ => 0) g x r leg ≠
    physicalBase d e even (J9FactorBounds.kernel L) (fun _ _ _ _ => 1) g x r leg := by
  intro he
  have hh := congrArg (fun p : Source[X] => (rationalMap (p.coeff 1))) he
  simp [physicalBase] at hh

#print axioms physical_base_at_original_center
#print axioms native_base_realized_by_own_tail
#print axioms native_crossing_realized_by_own_tail
#print axioms distinct_allowed_tails
end
end J6R14SpecializedBox
