import J6R9RecursiveProbes
import J6R9RecursiveReadout
import J6R9RecursiveNormalizer
import J6R9HermiteRing

/-! Concrete active Appendix D assembly in the two literal coefficient
quotients. Arithmetic follows child mode sums → binary probe interpolation
→ finite local quotient → exact rational Hermite combination → reduction.
The finite coefficients are lifted by their canonical double-monic
coordinate representatives when the input modulus is monic. -/
namespace J6R9Recursive
open scoped BigOperators Polynomial
open Polynomial J6ActiveSchedule J6ActiveRun J6ActiveUniqueness J6ActivePrintedHermite

noncomputable def representative (p : ℕ) (f : ℤ[X]) (ell : ℕ) (x : Box f ell p) :
    IntRing f ell := by
  classical
  exact if hf : f.Monic then canonicalLift p f hf ell x else Classical.choose (reduce_surj p f ell x)

theorem representative_spec (p : ℕ) (f : ℤ[X]) (ell : ℕ) (x : Box f ell p) :
    reduce p f ell (representative p f ell x) = x := by
  classical
  unfold representative
  split
  · exact canonicalLift_spec p f ‹f.Monic› ell x
  · exact Classical.choose_spec (reduce_surj p f ell x)

theorem coefficient_lift_congr (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ)
    (x : Box f ell p) (y : IntRing f ell) (h : x = reduce p f ell y) :
    (2:IntRing f ell)^p ∣ representative p f ell x-y := by
  apply (reduce_zero_iff p f hf ell _).mp
  rw [map_sub,representative_spec,h,sub_self]

/-- Read the actual nested monic coordinates of the reconstructed
rational value. This never needs the unknown true origin. -/
noncomputable def readIntegral (p : ℕ) (f : ℤ[X]) (ell : ℕ)
    (x : RatRing f ell) : Box f ell p := by
  classical
  exact if hf : f.Monic then rationalRead p f hf ell x else 0

theorem readIntegral_embed (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ)
    (x : IntRing f ell) :
    readIntegral p f ell (embed f ell x) = reduce p f ell x := by
  classical
  unfold readIntegral
  rw [dif_pos hf]
  exact rationalRead_exact p f hf ell x

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]

noncomputable def approxJet (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ)
    (c : Call Host) (fit : ProofFit S f c) (answers : Responses S f ell c)
    (t : ℤ) (j : ℕ) : IntRing f ell :=
  if ht : t ∈ active (S.levelBits c.depth) c.edges (S.levelWidth c.depth) then
    let τ : Center S c := ⟨t,ht⟩
    let p := registerPrecision S c τ
    let E' := integralE f ell (S.levelBits c.depth) c.edges (S.levelWidth c.depth) t
    representative p f ell ((quotientAt S f ell c fit answers τ (E'.map (reduce p f ell))).coeff j)
  else 0

noncomputable def assemble (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ)
    (c : Call Host) (fit : ProofFit S f c) (answers : Responses S f ell c) :
    Box f ell c.prec :=
  readIntegral c.prec f ell
    (J6R9Hermite.linearRecompose (S.levelBits c.depth) c.edges (S.levelWidth c.depth)
      (fun t j => embed f ell (approxJet S f ell c fit answers t j)))

/-- A finite active step without an assumed final answer. It requires:
(1) the degree bound, (2) integral local source representatives,
(3) exact grouped per-probe child semantics, (4) integrality of the origin.
All receiving maps and intermediate arithmetic are fixed above. -/
theorem assemble_exact (S : Shape Host Mode) (f : ℤ[X]) (hf : f.Monic)
    (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (ell : ℕ) (c : Call Host) (fit : ProofFit S f c)
    (hu : 0 < S.levelWidth c.depth) (huM : S.levelWidth c.depth ≤ c.edges)
    (F : (RatRing f ell)[X])
    (hdeg : F.natDegree ≤ J9PrintedSchedule.degreeBound c.edges (2^S.levelBits c.depth))
    (locals : ℤ → (IntRing f ell)[X])
    (integral : ∀ t ∈ active (S.levelBits c.depth) c.edges (S.levelWidth c.depth),
      (locals t).map (embed f ell) = atNode (dyadicUnit (S.levelBits c.depth)) (t:RatRing f ell) F)
    (out : IntRing f ell) (origin : F.eval 0 = embed f ell out)
    (answers : Responses S f ell c)
    (sample : ∀ (t : Center S c) (z : Probe S c),
      groupedSample S f ell c answers t z =
        ((locals t.val).map (reduce (registerPrecision S c t) f ell)).eval
          (sampleNode S f ell c fit t z)) :
    assemble S f ell c fit answers = reduce c.prec f ell out := by
  let a := S.levelBits c.depth
  let u := S.levelWidth c.depth
  let good := fun t j => (exactQuotient f ell a c.edges u t (locals t)).coeff j
  have hGood : J6R9Hermite.linearRecompose a c.edges u (fun t j => embed f ell (good t j))
      = embed f ell out := by
    rw [← origin]
    simp only [J6R9Hermite.linearRecompose,Algebra.smul_def,good]
    exact weighted_truth_origin f ell a c.edges u hu huM F hdeg locals integral
  have hApprox : ∀ t ∈ active a c.edges u, ∀ j < order c.edges u t,
      (2:IntRing f ell)^childPrecision c.prec a c.edges u t ∣
        approxJet S f ell c fit answers t j-good t j := by
    intro t ht j _
    let τ : Center S c := ⟨t,ht⟩
    let p := registerPrecision S c τ
    have hp : 0 < p := (Nat.zero_le c.prec).trans_lt
      (child_monotone c.prec a c.edges u t (hu.trans_le huM))
    have hloc : (locals t).natDegree ≤ J9PrintedSchedule.degreeBound c.edges (2^a) := by
      rw [← natDegree_map_eq_of_injective (embed_inj f hf ell),integral t ht]
      exact (atNode_degree _ _ F).trans hdeg
    unfold approxJet
    rw [dif_pos ht]
    apply coefficient_lift_congr p f hf ell
    change (quotientAt S f ell c fit answers τ
      ((integralE f ell a c.edges u t).map (reduce p f ell))).coeff j =
        reduce p f ell ((exactQuotient f ell a c.edges u t (locals t)).coeff j)
    rw [← Polynomial.coeff_map,exactQuotient]
    exact congrArg (fun P : (Box f ell p)[X] => P.coeff j)
      (quotientAt_exact S f hf hF ell c fit answers τ hp (reduce p f ell)
        (integralE f ell a c.edges u t) (locals t) hloc (sample τ))
  obtain ⟨actual,hActual,hd⟩ := J6R9Hermite.finite_ring_receive
    (embed f ell) (localScalar f ell) (embed_localScalar f ell) a c.edges u c.prec huM
    (approxJet S f ell c fit answers) good out hGood hApprox
  unfold assemble
  rw [← hActual,readIntegral_embed c.prec f hf ell]
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (reduce_zero_iff c.prec f hf ell _).mpr hd

#print axioms representative_spec
#print axioms coefficient_lift_congr
#print axioms readIntegral_embed
#print axioms assemble_exact
end J6R9Recursive