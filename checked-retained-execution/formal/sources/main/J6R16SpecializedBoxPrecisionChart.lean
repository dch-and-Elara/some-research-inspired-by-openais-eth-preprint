import J6R16SpecializedBoxPrecision
import J6R15SpecializedBoxNativeKernel
import J9R13PhysicalFusion

/-! The same physical high observation can be reduced from the printed
register precision q to a requested lower receiver p. This is not a
recompile of the parent's old creation tags. The finite inverse tails
are proved coherent even though the chosen polynomial depends on q. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial DenominatorBudget J8Physical J8EndToEnd J8J9Grouped
open NativeProbeRing DyadicProbeCompiler
noncomputable section
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type*} {U : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G U L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (U v)] [∀ v, DecidableEq (U v)]

theorem realizedKernel_lower_precision
    (a p q : ℕ) (hp : 0<p) (hpq : p≤q) (hW : L=2^a)
    (e : Even L) (hL : 2<L) (s : S) (n : ℕ)
    (f : ℤ[X]) (z : Scalar p f) (j : TargetPorts d s) :
    (physicalKernel d s e hL (J9FactorBounds.kernel L) n
      (fun j => (genuineCross d a q n e hL s j).divX) j).eval₂ (toScalar p f) (2*z) =
    (physicalKernel d s e hL (J9FactorBounds.kernel L) n
      (fun j => (genuineCross d a p n e hL s j).divX) j).eval₂ (toScalar p f) (2*z) := by
  rw [genuine_kernel_is_own_divX d a q (hp.trans_le hpq) hW e hL s n,
    genuine_kernel_is_own_divX d a p hp hW e hL s n]
  unfold genuineCross
  by_cases hj : j∈groupedTargets d s
  · rw [dif_pos hj,dif_pos hj]
    simp only [Polynomial.eval₂_map]
    exact modeHalf_lower_precision a p q hpq (scalar_nilpotent p f) _ _ _ _
      ((toScalar p f).comp twoLocalToSource.toRingHom) z
  · rw [dif_neg hj,dif_neg hj]

theorem genuine_high_modulus_coherent
    (e : EndpointSeating d) (he : Even L) (hL : 2<L) (s : S)
    (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (n : Fin (Fintype.card (PinTile d s))) (a p q : ℕ)
    (hp : 0<p) (hpq : p≤q) (hW : L=2^a) (f : ℤ[X]) (adr : Fin f.natDegree→Bool) :
    reduceScalar p q hpq f
      (highObservation d e he hL s F sign tail n
        (fun j => (genuineCross d a q n.val he hL s j).divX) a q f adr) =
      highObservation d e he hL s F sign tail n
        (fun j => (genuineCross d a p n.val he hL s j).divX) a p f adr := by
  unfold highObservation
  rw [groupedProbe_reduce]
  unfold groupedProbe
  refine congrArg (fun X : Scalar p f => _ * X) ?_
  refine Finset.sum_congr rfl ?_
  intro j _
  dsimp only
  rw [realizedKernel_lower_precision d a p q hp hpq hW he hL s n.val f (probe p f adr) j]

#print axioms realizedKernel_lower_precision
#print axioms genuine_high_modulus_coherent
end
end J6R14SpecializedBox