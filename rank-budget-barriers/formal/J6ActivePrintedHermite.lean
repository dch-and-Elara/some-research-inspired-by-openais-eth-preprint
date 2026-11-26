import J6ActiveHermite
import J6ActiveSchedule

/-! The literal Appendix D Hermite formula on the actual signed grid
with the printed scaled coordinate and taper schedule. This is the
exact characteristic-zero recovery statement; finite precision of the
last rational-weighted assembly is a separate assertion. -/
namespace J6ActivePrintedHermite
open scoped BigOperators Polynomial
open Polynomial J6ActiveUniqueness J6ActiveHermite J6ActiveSchedule

variable {R : Type*} [CommRing R] [Algebra ℚ R]

noncomputable def dyadicUnit (a : ℕ) : Rˣ :=
  Units.map (algebraMap ℚ R).toMonoidHom
    (Units.mk0 ((2:ℚ)^(a+1)) (pow_ne_zero _ (by decide)))

noncomputable def invDiff (t q : ℤ) : R :=
  algebraMap ℚ R (((t:ℚ)-(q:ℚ))⁻¹)

theorem invDiff_spec {t q : ℤ} (h : t ≠ q) :
    invDiff (R:=R) t q * ((t:R)-(q:R)) = 1 := by
  have hn : (t:ℚ)-(q:ℚ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr h
  have hcast : (t:R)-(q:R) = algebraMap ℚ R ((t:ℚ)-(q:ℚ)) := by simp
  rw [invDiff, hcast, ← map_mul, inv_mul_cancel₀ hn, map_one]

theorem printed_origin [Nontrivial R] (a M u : ℕ)
    (hu : 0 < u) (huM : u ≤ M) (F : R[X])
    (hdeg : F.natDegree ≤ J9PrintedSchedule.degreeBound M (2^a)) (sample : ℤ → R[X])
    (hs : ∀ t ∈ active a M u, ∀ j < order M u t,
      (sample t).coeff j = (atNode (dyadicUnit a) (t:R) F).coeff j) :
    let s := active a M u
    let k := order M u
    let eg := normalizer s (fun t : ℤ => (t:R)) k invDiff
    (∑ t ∈ s, (eg t).eval 0 *
      (dividedJet (k t) (atNode (dyadicUnit a) (t:R) (eg t)) (sample t)).eval
        ((↑(dyadicUnit (R:=R) a)⁻¹ : R) * (-(t:R)))) = F.eval 0 := by
  dsimp only
  simpa only [zero_sub] using recover_at (active a M u)
    (fun t : ℤ => (t:R)) (order M u) invDiff (dyadicUnit a) F sample 0
    (fun t ht => active_order_pos a M u t ht)
    (fun t _ q hq => invDiff_spec ((Finset.mem_erase.mp hq).1.symm))
    (hdeg.trans_lt (total_order_large a M u hu huM)) hs

#print axioms invDiff_spec
#print axioms printed_origin
end J6ActivePrintedHermite