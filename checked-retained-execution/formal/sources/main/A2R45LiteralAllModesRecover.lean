
import J6R9RecursiveAssemble

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5500000
set_option maxRecDepth 2050
set_option linter.unusedSectionVars false

/-! Original v9 A2, lines 2331--2354: client of one *completed
all-mode sum* per actual (centre, binary probe), not simulated fine
child answers. Use exactly the stock coordinates, local normalizer
and tapered Hermite assembly from J6R9Recursive. -/
namespace A2R45Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R9Recursive J6ActiveRun J6ActiveSchedule
open J6ActiveUniqueness J6ActivePrintedHermite

noncomputable section
variable {Host Mode : Type*}

abbrev WholeAnswers (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host) :=
  ∀ t : Center S c, Probe S c → Box f ell (registerPrecision S c t)

def wholeApprox (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (vals : WholeAnswers S f ell c) (t : ℤ) (j : ℕ) : IntRing f ell :=
  if ht : t∈active (S.levelBits c.depth) c.edges (S.levelWidth c.depth) then
    let τ : Center S c := ⟨t,ht⟩
    let p := registerPrecision S c τ
    let E' := integralE f ell (S.levelBits c.depth) c.edges (S.levelWidth c.depth) t
    let P := J6ActiveInterpolation.decoded (sampleNode S f ell c fit τ) (vals τ)
    representative p f ell
      ((J6ActiveNormalizer.quotientJet (order c.edges (S.levelWidth c.depth) t)
        (E'.map (reduce p f ell)) P).coeff j)
  else 0

def wholeAssemble (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (vals : WholeAnswers S f ell c) : Box f ell c.prec :=
  readIntegral c.prec f ell
    (J6R9Hermite.linearRecompose (S.levelBits c.depth) c.edges (S.levelWidth c.depth)
      (fun t j=>embed f ell (wholeApprox S f ell c fit vals t j)))

theorem unchanged_source_postprocessing [Fintype Mode] [DecidableEq Mode]
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (answers : Responses S f ell c) :
    wholeAssemble S f ell c fit (groupedSample S f ell c answers) =
      assemble S f ell c fit answers := rfl

theorem wholeAssemble_exact (S : Shape Host Mode) (f : ℤ[X]) (hf : f.Monic)
    (hF : 0<f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (ell : ℕ) (c : Call Host) (fit : ProofFit S f c)
    (hu : 0<S.levelWidth c.depth) (huM : S.levelWidth c.depth≤c.edges)
    (F : (RatRing f ell)[X])
    (hdeg : F.natDegree≤J9PrintedSchedule.degreeBound c.edges (2^S.levelBits c.depth))
    (loc : ℤ→(IntRing f ell)[X])
    (integral : ∀ t∈active (S.levelBits c.depth) c.edges (S.levelWidth c.depth),
      (loc t).map (embed f ell)=atNode (dyadicUnit (S.levelBits c.depth)) (t:RatRing f ell) F)
    (out : IntRing f ell) (origin : F.eval 0=embed f ell out)
    (vals : WholeAnswers S f ell c)
    (oracle : ∀ t z, vals t z =
      ((loc t.val).map (reduce (registerPrecision S c t) f ell)).eval
        (sampleNode S f ell c fit t z)) :
    wholeAssemble S f ell c fit vals=reduce c.prec f ell out := by
  let a := S.levelBits c.depth
  let u := S.levelWidth c.depth
  let good := fun t j => (exactQuotient f ell a c.edges u t (loc t)).coeff j
  have hGood : J6R9Hermite.linearRecompose a c.edges u (fun t j=>embed f ell (good t j))
      = embed f ell out := by
    rw [←origin]
    simp only [J6R9Hermite.linearRecompose,Algebra.smul_def,good]
    exact weighted_truth_origin f ell a c.edges u hu huM F hdeg loc integral
  have hApprox : ∀ t∈active a c.edges u,∀ j<order c.edges u t,
      (2:IntRing f ell)^childPrecision c.prec a c.edges u t ∣
        wholeApprox S f ell c fit vals t j-good t j := by
    intro t ht j _
    let τ : Center S c := ⟨t,ht⟩
    let p := registerPrecision S c τ
    have hp : 0<p := (Nat.zero_le c.prec).trans_lt
      (child_monotone c.prec a c.edges u t (hu.trans_le huM))
    have hloc : (loc t).natDegree≤J9PrintedSchedule.degreeBound c.edges (2^a) := by
      rw [←natDegree_map_eq_of_injective (embed_inj f hf ell),integral t ht]
      exact (atNode_degree _ _ F).trans hdeg
    let L := (loc t).map (reduce p f ell)
    have hvals : vals τ = fun z => L.eval (sampleNode S f ell c fit τ z) :=
      funext (oracle τ)
    have hdec : J6ActiveInterpolation.decoded (sampleNode S f ell c fit τ) (vals τ)=L := by
      rw [hvals]
      exact J6ActiveInterpolation.decoded_exact _ _ (natDegree_map_le.trans hloc)
        (fun i j h=>J6ActiveInterpolation.node_pair_units p hp f hf hF ell _ fit i j h)
    unfold wholeApprox
    rw [dif_pos ht]
    apply coefficient_lift_congr p f hf ell
    change (J6ActiveNormalizer.quotientJet (order c.edges u t)
      ((integralE f ell a c.edges u t).map (reduce p f ell))
      (J6ActiveInterpolation.decoded (sampleNode S f ell c fit τ) (vals τ))).coeff j =
        reduce p f ell ((exactQuotient f ell a c.edges u t (loc t)).coeff j)
    rw [hdec,←Polynomial.coeff_map,exactQuotient]
    exact congrArg (fun Q : (Box f ell p)[X]=>Q.coeff j)
      (J6ActiveNormalizer.quotientJet_map (reduce p f ell) (order c.edges u t)
        (integralE f ell a c.edges u t) (loc t)).symm
  obtain ⟨actual,hActual,hd⟩ := J6R9Hermite.finite_ring_receive
    (embed f ell) (localScalar f ell) (embed_localScalar f ell) a c.edges u c.prec huM
    (wholeApprox S f ell c fit vals) good out hGood hApprox
  unfold wholeAssemble
  rw [←hActual,readIntegral_embed c.prec f hf ell]
  apply sub_eq_zero.mp
  rw [←map_sub]
  exact (reduce_zero_iff c.prec f hf ell _).mpr hd

#print axioms unchanged_source_postprocessing
#print axioms wholeAssemble_exact
end
end A2R45Literal
