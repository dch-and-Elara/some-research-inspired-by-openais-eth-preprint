import P5P3NativeCriterion
import P5P3Readout

/-! P.2 on the actual printed dyadic root geometry. The budget controls
only the fixed retained-jet decoder under independent errors; no
asymptotic profile optimization or alternative decoder is asserted. -/
namespace Paper5.P3
open P1DyadicGrid HermiteLoss
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]

def printedDegree (u M : ℕ) : ℕ := M*(2*2^(2*u)-1)

def printedHeight (u M : ℕ) : ℕ := (3*M+u-1)/u

theorem printed_root_window_p2 (O : Subring K) [IsLocalRing O] (hn2 : ¬IsUnit (2:O))
    (u M p b : ℕ) (q : (rootNodes u)→ℕ) (ha : (activeNodes q).Nonempty) :
    (degreeAdmissible q (printedDegree u M) b ∧
      ActualCertified O (fun t : rootNodes u => nativeCenter (2*u) t.val) q b
        (fun s t => nativeDifference_integral_inverses O hn2 (2*u) s.val t.val
          (Finset.mem_filter.mp s.property).1 (Finset.mem_filter.mp t.property).1)
        (fun t => (↑(twoUnit K^rootPrecision u M (printedHeight u M) p t.val):K))
        (↑(twoUnit K^(p:ℤ)):K)) ↔
    (0<b ∧ (b:ℤ) ≤ largestBound q (printedDegree u M)
         (fun t => rootPrecision u M (printedHeight u M) p t.val)
         (fun t => nativeLoss (2*u) t.val) (nativeCarrierVal Subtype.val q) p ha) := by
  by_cases hb : 0<b
  · rw [printed_root_p1 O hn2 u M (printedHeight u M) p b hb q]
    exact window_cap_p2 q _ b _ _ _ p ha (fun t _ =>
      native_loss_positive (Finset.mem_filter.mp t.property).1 (Finset.mem_filter.mp t.property).2.1)
  · simp [degreeAdmissible,hb]

#print axioms printed_root_window_p2
end Paper5.P3
