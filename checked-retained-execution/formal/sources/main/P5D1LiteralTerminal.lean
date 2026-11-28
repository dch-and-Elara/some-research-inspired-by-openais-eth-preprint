import P5D1LiteralReply

/-! Exact unreduced Appendix D field-form expression of the finite
reply table. The same fixed Hermite losses apply to the early lifts
because their decoded residues are unchanged. -/
namespace Paper5.D1Literal
open scoped BigOperators
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive
open J6ActiveUniqueness J6ActivePrintedHermite

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]

noncomputable def normalAt
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host) (t : Center S c) :
    (Box f ell (registerPrecision S c t))[X] :=
  (integralE f ell (S.levelBits c.depth) c.edges (S.levelWidth c.depth) t.val).map
    (reduce (registerPrecision S c t) f ell)

noncomputable def earlyLift
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (answers : Responses S f ell c) (t : ℤ) (j : ℕ) : IntRing f ell :=
  if ht : t ∈ active (S.levelBits c.depth) c.edges (S.levelWidth c.depth) then
    let τ : Center S c := ⟨t,ht⟩
    if hj : j < order c.edges (S.levelWidth c.depth) t then
      liftedReply S f ell c fit answers τ (normalAt S f ell c τ) ⟨j,hj⟩
    else 0
  else 0

theorem earlyLift_on_active
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (answers : Responses S f ell c) (t : Center S c) (j : Orders S c t) :
    earlyLift S f ell c fit answers t.val j.val =
      liftedReply S f ell c fit answers t (normalAt S f ell c t) j := by
  unfold earlyLift
  rw [dif_pos t.property, dif_pos j.isLt]

noncomputable def originWeight
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (t : Center S c) (j : Orders S c t) : RatRing f ell :=
  algebraMap ℚ (RatRing f ell) (HermiteLoss.weight
    (S.levelBits c.depth) (S.levelWidth c.depth)
    (HermiteLoss.sourceH c.edges (S.levelWidth c.depth)) j.val t.val)

noncomputable def fieldMenuWeight
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (t : Center S c) (z : Probe S c) : RatRing f ell :=
  replyWeight S f ell c fit t (normalAt S f ell c t) (originWeight S f ell c t) z

noncomputable def nativeFieldMenuSum
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (answers : Responses S f ell c) : RatRing f ell :=
  ∑ t : Center S c, ∑ z : Probe S c, ∑ β : Terms S c t,
    fieldMenuWeight S f ell c fit t z *
      ∏ g : Fin 64, embed f ell (representative (registerPrecision S c t) f ell (answers ⟨t,z,β,g⟩))

set_option maxHeartbeats 6200000 in
theorem early_recompose_eq_field_menu
    (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) (c : Call Host)
    (fit : ProofFit S f c) (answers : Responses S f ell c) :
    J6R9Hermite.linearRecompose (S.levelBits c.depth) c.edges (S.levelWidth c.depth)
      (fun t j => embed f ell (earlyLift S f ell c fit answers t j)) =
      nativeFieldMenuSum S f ell c fit answers := by
  classical
  unfold J6R9Hermite.linearRecompose nativeFieldMenuSum
  rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Fin.sum_univ_eq_sum_range]
  rw [show (∑ z : Probe S c, ∑ β : Terms S c t, fieldMenuWeight S f ell c fit t z *
        ∏ g : Fin 64, embed f ell (representative (registerPrecision S c t) f ell
          (answers ⟨t,z,β,g⟩))) = ∑ j : Orders S c t, originWeight S f ell c t j *
            embed f ell (liftedReply S f ell c fit answers t (normalAt S f ell c t) j) from
    (liftedReply_one_product_per_address S f ell c fit answers t
      (normalAt S f ell c t) (originWeight S f ell c t)).symm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [earlyLift_on_active S f ell c fit answers t j, Algebra.smul_def, originWeight]

set_option maxHeartbeats 16000000 in
theorem native_field_menu_integral
    (S : Shape Host Mode) (f : ℤ[X]) (hf : f.Monic)
    (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (ell : ℕ) (c : Call Host) (fit : ProofFit S f c)
    (hu : 0 < S.levelWidth c.depth) (huM : S.levelWidth c.depth ≤ c.edges)
    (F : (RatRing f ell)[X])
    (hdeg : F.natDegree ≤ J9PrintedSchedule.degreeBound c.edges (2^S.levelBits c.depth))
    (locals : ℤ → (IntRing f ell)[X])
    (integral : ∀ t ∈ active (S.levelBits c.depth) c.edges (S.levelWidth c.depth),
      (locals t).map (embed f ell) = atNode (dyadicUnit (S.levelBits c.depth)) (t:RatRing f ell) F)
    (truth : IntRing f ell) (origin : F.eval 0 = embed f ell truth)
    (answers : Responses S f ell c)
    (sample : ∀ (t : Center S c) (z : Probe S c),
      groupedSample S f ell c answers t z =
        ((locals t.val).map (reduce (registerPrecision S c t) f ell)).eval
          (sampleNode S f ell c fit t z)) :
    ∃ out : IntRing f ell, embed f ell out = nativeFieldMenuSum S f ell c fit answers ∧
      (2 : IntRing f ell)^c.prec ∣ out - truth := by
  let a := S.levelBits c.depth
  let u := S.levelWidth c.depth
  let good := fun t j => (exactQuotient f ell a c.edges u t (locals t)).coeff j
  have hGood : J6R9Hermite.linearRecompose a c.edges u (fun t j => embed f ell (good t j))
      = embed f ell truth := by
    rw [← origin]
    simp only [J6R9Hermite.linearRecompose, Algebra.smul_def, good]
    exact weighted_truth_origin f ell a c.edges u hu huM F hdeg locals integral
  have hApprox : ∀ t ∈ active a c.edges u, ∀ j < order c.edges u t,
      (2 : IntRing f ell)^childPrecision c.prec a c.edges u t ∣
        earlyLift S f ell c fit answers t j - good t j := by
    intro t ht j hj
    let τ : Center S c := ⟨t,ht⟩
    let jj : Orders S c τ := ⟨j,hj⟩
    let p := registerPrecision S c τ
    have hp : 0 < p := (Nat.zero_le c.prec).trans_lt
      (child_monotone c.prec a c.edges u t (hu.trans_le huM))
    have hloc : (locals t).natDegree ≤ J9PrintedSchedule.degreeBound c.edges (2^a) := by
      rw [← natDegree_map_eq_of_injective (embed_inj f hf ell),integral t ht]
      exact (atNode_degree _ _ F).trans hdeg
    change (2 : IntRing f ell)^p ∣ earlyLift S f ell c fit answers τ.val jj.val - good t j
    apply (reduce_zero_iff p f hf ell _).mp
    rw [map_sub, earlyLift_on_active S f ell c fit answers τ jj, liftedReply_reduce]
    have hq := quotientAt_exact S f hf hF ell c fit answers τ hp (reduce p f ell)
      (integralE f ell a c.edges u t) (locals t) hloc (sample τ)
    change (quotientAt S f ell c fit answers τ
      ((integralE f ell a c.edges u t).map (reduce p f ell))).coeff j -
        reduce p f ell (good t j) = 0
    rw [hq, Polynomial.coeff_map]
    exact sub_self _
  obtain ⟨out, hout, hd⟩ := J6R9Hermite.finite_ring_receive
    (embed f ell) (localScalar f ell) (embed_localScalar f ell) a c.edges u c.prec huM
    (earlyLift S f ell c fit answers) good truth hGood hApprox
  exact ⟨out, hout.trans (early_recompose_eq_field_menu S f ell c fit answers), hd⟩

#print axioms earlyLift_on_active
#print axioms early_recompose_eq_field_menu
#print axioms native_field_menu_integral
end Paper5.D1Literal

