import J6R10IntegralFinite

/-! Attach the literal polynomial and its finite sample to the actual
R9 recursive verifier. This removes free choices of the rational
deformation, integral jets, degree bound and origin equation. The only
arithmetic hypothesis that remains about children is their finite
grouped register sum versus the explicit ungrouped evaluation. -/
namespace J6R10Integral
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid J6ActiveRun J6ActiveSchedule J6R9Recursive

variable {Host Mode K : Type*} [Fintype Mode] [DecidableEq Mode] [DecidableEq K]
variable {S : Shape Host Mode} {f : ℤ[X]} {ell : ℕ} {B : Blueprint S f ell}

/-- Physical incidence choices and the two unmultiplied sides of every
parent are supplied. The shape uses all real edges (not padded slots).
Finite tensors are supplied at the current call precision; the exact
entries in the reference contraction are their canonical lifts. -/
structure SourceLayout (K : Type*) (B : Blueprint S f ell) (hf : f.Monic) where
  Valid : Call Host → Prop
  child_valid : ∀ c, Valid c → S.cutoff < c.edges → ∀ w, Valid (B.program.child c w)
  fit : ∀ c, Valid c → S.cutoff < c.edges → ProofFit S f c
  taper : ∀ c, Valid c → S.cutoff < c.edges →
    0 < S.levelWidth c.depth ∧ S.levelWidth c.depth ≤ c.edges
  atlas : ∀ c : Call Host, Atlas (Fin c.edges) K (S.levelBits c.depth)
  left : ∀ c : Call Host, (Fin c.edges → Bool) → List (Box f ell c.prec)
  right : ∀ c : Call Host, (Fin c.edges → Bool) → List (Box f ell c.prec)
  split_entries : ∀ c, Valid c → S.cutoff < c.edges → ∀ y,
    (B.entries c y).prod =
      ((left c y ++ right c y).map (canonicalLift c.prec f hf ell)).prod

variable {hf : f.Monic}

noncomputable def SourceLayout.leftLift (D : SourceLayout K B hf) (c : Call Host)
    (x : Fin c.edges → Bool) : IntRing f ell :=
  liftedProduct c.prec f hf ell (D.left c x)

noncomputable def SourceLayout.rightLift (D : SourceLayout K B hf) (c : Call Host)
    (x : Fin c.edges → Bool) : IntRing f ell :=
  liftedProduct c.prec f hf ell (D.right c x)

noncomputable def SourceLayout.nativeSample (D : SourceLayout K B hf) (c : Call Host)
    (fit : ProofFit S f c) (t : Center S c) (z : Probe S c) :
    Box f ell (registerPrecision S c t) :=
  let p := registerPrecision S c t
  contract (finiteEntry p f ell (D.atlas c) t.val (sampleNode S f ell c fit t z))
    (reduce p f ell ∘ D.leftLift c) (reduce p f ell ∘ D.rightLift c)

/-- Direct finite grouped-semantics interface. The terms here are the
actual reference evaluations on child inputs, not oracles in the
resulting program. -/
def SourceLayout.ExactGrouped (D : SourceLayout K B hf) : Prop :=
  ∀ c (hc : D.Valid c) (h : S.cutoff < c.edges) (t : Center S c) (z : Probe S c),
    groupedSample S f ell c (fun w => B.expect (B.program.child c w)) t z =
      D.nativeSample c (D.fit c hc h) t z

noncomputable def SourceLayout.sourceSpec (D : SourceLayout K B hf)
    (grouped : D.ExactGrouped) : B.SourceSpec where
  Valid := D.Valid
  child_valid := D.child_valid
  deformation := fun c => globalNetwork f ell (D.atlas c) (D.leftLift c) (D.rightLift c)
  jets := fun c t => integralNetwork f ell (D.atlas c) t (D.leftLift c) (D.rightLift c)
  fit := D.fit
  taper := D.taper
  degree := by
    intro c _ _
    simpa only [Fintype.card_fin] using network_degree f ell (D.atlas c) (D.leftLift c) (D.rightLift c)
  integral := by
    intro c _ _ t
    have ht : t.val ∈ grid (S.levelBits c.depth) :=
      (active_grid _ _ _ t.property).1
    exact network_embed f ell (D.atlas c) ht (D.leftLift c) (D.rightLift c)
  origin := by
    intro c hc h
    rw [network_origin,Blueprint.truth]
    congr 1
    apply Finset.sum_congr
    · ext y
      simp only [Finset.mem_univ]
    · intro y _
      rw [D.split_entries c hc h y,List.map_append,List.prod_append]
      rfl
  grouped := by
    intro c hc h t z
    rw [network_finite]
    exact grouped c hc h t z

theorem SourceLayout.run_exact (D : SourceLayout K B hf) (grouped : D.ExactGrouped)
    (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (c : Call Host) (hc : D.Valid c) :
    B.program.run c = reduce c.prec f ell (B.truth c) :=
  B.run_exact (D.sourceSpec grouped) hf hF c hc

#print axioms SourceLayout.sourceSpec
#print axioms SourceLayout.run_exact
end J6R10Integral
