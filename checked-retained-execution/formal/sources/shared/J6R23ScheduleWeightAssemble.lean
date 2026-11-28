import J6R23ScheduleWeightSum
import J6R10IntegralFinite

/-! The weighted pass produces the genuine shifted high-precision
register for the original active assembly, not merely a collection
of valid weights. The same source degree, local integral profile,
and actual recursively grouped sample identities used by R9 are
explicit. This does not claim to generate the entire recursion's
descriptor and directory supply. -/
namespace J6R23ScheduleWeight
open scoped Polynomial BigOperators Classical
open Polynomial A1R10 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R9Hermite
open J6R22Active J6ActiveUniqueness J6ActivePrintedHermite HermiteLoss

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]

set_option maxHeartbeats 1900000 in
theorem actual_active_high
    (S : Shape Host Mode) {f : ℤ[X]} (hf : f.Monic) (he : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (ell : ℕ) (c : Call Host) (fit : ProofFit S f c) (B : ℕ)
    (hu : 0<S.levelWidth c.depth) (huM : S.levelWidth c.depth≤c.edges)
    (hB : commonLoss (S.levelBits c.depth) c.edges (S.levelWidth c.depth)≤B)
    (answers : Responses S f ell c)
    (Φ : (RatRing f ell)[X])
    (deg : Φ.natDegree≤J9PrintedSchedule.degreeBound c.edges (2^S.levelBits c.depth))
    (locals : ℤ→(IntRing f ell)[X])
    (localize : ∀ t∈active (S.levelBits c.depth) c.edges (S.levelWidth c.depth),
      (locals t).map (embed f ell)=atNode (dyadicUnit (S.levelBits c.depth)) (t:RatRing f ell) Φ)
    (out : IntRing f ell) (origin : Φ.eval 0=embed f ell out)
    (sample : ∀ (t : Center S c) (z : Probe S c),
      groupedSample S f ell c answers t z =
        ((locals t.val).map (reduce (registerPrecision S c t) f ell)).eval (sampleNode S f ell c fit t z))
    (hq : 0<c.prec+B) {fw : List (Word (c.prec+B))}
    (hF : Modulus (c.prec+B) hq fw=NativeProbeRing.liftPoly (c.prec+B) f)
    (xs : List (ℤ×ℕ))
    (nd : (xs.map Prod.fst).Nodup)
    (cv : (xs.map Prod.fst).toFinset=active (S.levelBits c.depth) c.edges (S.levelWidth c.depth))
    (co : ∀ t∈xs,t.2=order c.edges (S.levelWidth c.depth) t.1)
    (term : ℤ→ℕ→Meter (UVBlock fw ell))
    (read : ∀ t∈xs,∀ j<t.2,boxTransport hF (uvRead hq fw ell (term t.1 j).result)=
      reduce (c.prec+B) f ell
        (localScalar f ell (scaledWeight (S.levelBits c.depth) (S.levelWidth c.depth)
          (sourceH c.edges (S.levelWidth c.depth)) B j t.1)*approxJet S f ell c fit answers t.1 j)) :
    let z := allTerms hq term xs
    boxTransport hF (uvRead hq fw ell z.result)=
      (2:Box f ell (c.prec+B))^B*reduce (c.prec+B) f ell out ∧
    z.steps≤termBill term xs+termsLoopFee fw.length ell (c.prec+B) hq xs := by
  let a := S.levelBits c.depth
  let u := S.levelWidth c.depth
  let approx := approxJet S f ell c fit answers
  let good := fun t j=>(exactQuotient f ell a c.edges u t (locals t)).coeff j
  have he0 : linearRecompose a c.edges u (fun t j=>embed f ell (good t j))=embed f ell out := by
    rw [←origin]
    simp only [linearRecompose,Algebra.smul_def,good]
    exact weighted_truth_origin f ell a c.edges u hu huM Φ deg locals localize
  have heD : ∀ t∈active a c.edges u,∀ j<order c.edges u t,
      (2:IntRing f ell)^childPrecision c.prec a c.edges u t ∣ approx t j-good t j := by
    intro t ht j _
    let τ : Center S c := ⟨t,ht⟩
    let p := registerPrecision S c τ
    have hp : 0<p := (Nat.zero_le c.prec).trans_lt
      (child_monotone c.prec a c.edges u t (hu.trans_le huM))
    have hd : (locals t).natDegree≤J9PrintedSchedule.degreeBound c.edges (2^a) := by
      rw [←natDegree_map_eq_of_injective (embed_inj f hf ell),localize t ht]
      exact (atNode_degree _ _ Φ).trans deg
    unfold approx approxJet
    rw [dif_pos ht]
    apply coefficient_lift_congr p f hf ell
    change (quotientAt S f ell c fit answers τ
      ((integralE f ell a c.edges u t).map (reduce p f ell))).coeff j =
      reduce p f ell ((exactQuotient f ell a c.edges u t (locals t)).coeff j)
    rw [←Polynomial.coeff_map,exactQuotient]
    exact congrArg (fun P : (Box f ell p)[X]=>P.coeff j)
      (quotientAt_exact S f hf he ell c fit answers τ hp (reduce p f ell)
        (integralE f ell a c.edges u t) (locals t) hd (sample τ))
  refine ⟨?_,allTerms_steps hq term xs⟩
  have hR := allTerms_scaled_register hq hF a c.edges u B xs term nd cv co approx read
  change boxTransport hF (uvRead hq fw ell (allTerms hq term xs).result)=_
  rw [hR]
  exact scaled_recompose_actual_register (embed f ell) (embed_inj f hf ell) (localScalar f ell)
    (embed_localScalar f ell) a c.edges u c.prec B hu huM hB approx good out
    (reduce (c.prec+B) f ell) (J6R10Integral.box_two_nil (c.prec+B) f ell) he0 heD

#print axioms actual_active_high
end J6R23ScheduleWeight


