import J6R23ScheduleWeightBridge

/-! One actual active transition through the source's fully specified
finite quotient receipts, weighted common register, and checked low
word reconstruction. This is a semantically equal modular
implementation of the source's rational combine; query/descriptor
supply and complete recursion are not inferred from this receipt. -/
namespace J6R23ScheduleWeight
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6ActiveUniqueness J6ActivePrintedHermite
open J6R22Active J6R19Retained HermiteLoss

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]

set_option maxHeartbeats 1900000 in
theorem active_finish_is_source
    (S : Shape Host Mode) {f : ℤ[X]} (hf : f.Monic) (he : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (ell : ℕ) (hv : 0<ell) (c : Call Host) (fit : ProofFit S f c) (B : ℕ)
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
    (hp : 0<c.prec) (hq : 0<c.prec+B) {high : List (Word (c.prec+B))} {low : List (Word c.prec)}
    (hH : Modulus (c.prec+B) hq high=NativeProbeRing.liftPoly (c.prec+B) f)
    (hL : Modulus c.prec hp low=NativeProbeRing.liftPoly c.prec f)
    (xs : List (ℤ×ℕ))
    (nd : (xs.map Prod.fst).Nodup)
    (cv : (xs.map Prod.fst).toFinset=active (S.levelBits c.depth) c.edges (S.levelWidth c.depth))
    (co : ∀ t∈xs,t.2=order c.edges (S.levelWidth c.depth) t.1)
    (term : ℤ→ℕ→Meter (UVBlock high ell))
    (read : ∀ t∈xs,∀ j<t.2,boxTransport hH (uvRead hq high ell (term t.1 j).result)=
      reduce (c.prec+B) f ell
        (localScalar f ell (scaledWeight (S.levelBits c.depth) (S.levelWidth c.depth)
          (sourceH c.edges (S.levelWidth c.depth)) B j t.1)*approxJet S f ell c fit answers t.1 j)) :
    let hh := (size_of_monic_words hq hf hH).trans (size_of_monic_words hp hf hL).symm
    let run := activeFinishM hq hh xs term
    ∃ u, run.result=some u ∧ boxTransport hL (uvRead hp low ell u)=assemble S f ell c fit answers ∧
      run.steps≤termBill term xs+termsLoopFee high.length ell (c.prec+B) hq xs+
        (6+ell*(10+high.length*(8*(c.prec+B+1)+c.prec+8)+low.length*c.prec))+4 := by
  obtain ⟨hi,_⟩ := actual_active_high S hf he ell c fit B hu huM hB answers Φ deg locals localize
    out origin sample hq hH xs nd cv co term read
  obtain ⟨u,ret,result,cost⟩ := activeFinish_value hp hq hv hf he hH hL xs term out hi
  refine ⟨u,ret,?_,cost⟩
  exact result.trans (assemble_exact S f hf he ell c fit hu huM Φ deg locals localize out origin
    answers sample).symm

#print axioms active_finish_is_source
end J6R23ScheduleWeight

