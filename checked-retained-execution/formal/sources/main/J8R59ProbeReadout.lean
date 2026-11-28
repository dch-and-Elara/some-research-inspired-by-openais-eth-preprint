import J9EndProbe
import J6R14ZeroModeProbe

/-! J8 interpolation takes an arbitrary list of distinct actual binary
representatives. In particular the list may include or omit zero. -/
namespace J8R59
open scoped BigOperators Polynomial Classical
open Polynomial NativeProbeRing DyadicProbeCompiler J9End
noncomputable section

/-- An arbitrary ordered collection of genuine binary coordinate lifts. -/
abbrev Roster (f : ℤ[X]) (I : Type*) := I ↪ (Fin f.natDegree → Bool)

def positiveRoster {f : ℤ[X]} {D : ℕ} (P : J6R14ZeroMode.Prescribed f D) :
    Roster f (Fin (D+1)) := ⟨P.word,P.distinct⟩

theorem roster_units {I : Type*} (p : ℕ) (hp : 0<p) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0<f.natDegree) [Fact (Irreducible (residuePoly f))]
    (W : Roster f I) :
    ∀ i j, i≠j → IsUnit (probe p f (W j)-probe p f (W i)) := by
  intro i j hij
  apply unit_of_residue p hp f hf
  rw [map_sub,sub_ne_zero]
  exact fun same => hij (W.injective ((binary_residues_injective p hp f hf hd) same.symm))

variable {A K : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K]

theorem observations_decode_for_roster (p q : ℕ) (hp : 0<p) (hpq : p≤q) (f : ℤ[X])
    (hf : f.Monic) (hd : 0<f.natDegree) [Fact (Irreducible (residuePoly f))]
    (W : Roster f (Fin (p+1)))
    (F : LiteralPortCompiler.CNF A) (base : (A → Bool) → A → Source[X])
    (kernel : (A → Bool) → A → K → Source[X]) (e : K → ℕ) (m : K) (hv : 1≤e m) :
    let x := fun i => probe p f (W i)
    let obs := fun i => reduceScalar p q hpq f (observation q f (W i) F base kernel e m)
    NativeInterpolation.decode x obs ⟨1, by omega⟩ =
      (2 : Scalar p f)^e m * toScalar p f
        ((MvPolynomial.coeff (Finsupp.single m 1)
          (LiteralPortCompiler.completed F base kernel)).coeff 0) := by
  dsimp only
  simp only [observation_reduce]
  exact DyadicSlotCompiler.decode_compiled_singleton (toScalar p f) p hp
    (scalar_nilpotent p f) F base kernel e m hv _ (roster_units p hp f hf hd W)


variable {L M : ℕ} {R T : Type*} [Fintype R] [DecidableEq R] [Fintype T]

/-- The exact source-localization identity, not a finite-ring congruence,
is the input here. The cleared residue, size bound, and signed recovery
are then all derived. -/
theorem recover_literal_first_at_roster
    (g : J9FactorBounds.Chart L M R T) (b : ℕ) (hL : 3 ≤ L)
    (hEven : L % 2 = 0) (hb : b < L) (hCube : L^3 ≤ M)
    (hpar : ∀ i ∈ g.targets, i.val%2=g.tau.val%2)
    (hTile : Function.Injective g.tileSlot)
    (hOne : ∀ r, ¬ (g.hit r false = true ∧ g.hit r true = true))
    (hCount : L * (J9FactorBounds.activeRows g).card ≤ 3*M)
    (rows : (Fin M → Bool) → R → Bool → ℚ[X]) (cross : Fin L → ℚ[X])
    (source : (Fin M → Bool) → ℚ[X])
    (q : ℕ) (hpq : 10*M ≤ q) (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    [Fact (Irreducible (residuePoly f))] (W : Roster f (Fin (10*M+1)))
    (F : LiteralPortCompiler.CNF A) (base : (A → Bool) → A → Source[X])
    (kernel : (A → Bool) → A → K → Source[X]) (e : K → ℕ) (m : K) (hv : 1 ≤ e m)
    (exactSource :
      algebraMap ℤ Source (J9FactorBounds.publicDenominator g b) *
        (2 : Source)^e m *
        (MvPolynomial.coeff (Finsupp.single m 1) (LiteralPortCompiler.completed F base kernel)).coeff 0 =
      algebraMap ℤ Source (J9FactorBounds.exactCleared g b)) :
    let p := 10*M
    have hp : 0 < p := by
      dsimp [p]; have he : 0 < L^3 := by positivity
      omega
    let x := fun i => probe p f (W i)
    let obs := fun i => reduceScalar p q hpq f
      (observation q f (W i) F base kernel e m)
    ((projectBase p f hf ((J9FactorBounds.publicDenominator g b : Scalar p f) *
      NativeInterpolation.decode x obs ⟨1, by omega⟩)).valMinAbs : ℚ) /
      J9FactorBounds.publicDenominator g b = (literalCompleted g b rows cross source).coeff 1 := by
  dsimp only
  let p := 10*M
  have hp : 0 < p := by
    have he : 0 < L^3 := by positivity
    dsimp [p]
    omega
  let D := J9FactorBounds.publicDenominator g b
  let a := J9FactorBounds.exactCleared g b
  let φ := toScalar p f
  have hD (n : ℤ) : φ (algebraMap ℤ Source n) = (n : Scalar p f) := by
    simp [φ, toScalar]
  have hres := congrArg φ exactSource
  simp only [map_mul,map_pow,map_ofNat,hD] at hres
  have hrange := J9FactorBounds.actual_factors_centered g b hL hEven hb hCube hpar hTile hOne hCount
  have hclear := (J9FactorBounds.cleared_exact_odd g b hL hEven hpar).2
  have hd0 : (D : ℚ) ≠ 0 := by
    have hpos : 0 < D := Finset.prod_pos
      (fun i hi => (J9FactorBounds.local_den_positive_odd g b hL hEven hpar i hi).1)
    exact_mod_cast hpos.ne'
  have hc : (a : ℚ) = (D : ℚ) * (literalCompleted g b rows cross source).coeff 1 := by
    rw [literal_first_exact]
    exact hclear
  rw [observations_decode_for_roster p q hp hpq f hf hd W F base kernel e m hv, ← mul_assoc]
  change ((projectBase p f hf ((D : Scalar p f) * (2 : Scalar p f)^e m *
        φ ((MvPolynomial.coeff (Finsupp.single m 1)
          (LiteralPortCompiler.completed F base kernel)).coeff 0))).valMinAbs : ℚ) / D = _
  rw [show (D : Scalar p f) * (2 : Scalar p f)^e m *
      φ ((MvPolynomial.coeff (Finsupp.single m 1)
        (LiteralPortCompiler.completed F base kernel)).coeff 0) = (a : Scalar p f) from hres]
  have hx : projectBase p f hf (a : Scalar p f) = (a : Base p) := by
    rw [← map_intCast (AdjoinRoot.of (liftPoly p f)) a, projectBase_left p hp f hf hd]
  rw [hx]
  haveI : NeZero (2^p : ℕ) := ⟨pow_ne_zero _ (by decide)⟩
  have hcint : (↑((2:ℕ)^p) : ℤ) = (2:ℤ)^p := by norm_cast
  have hmin := (ZMod.valMinAbs_spec (a : Base p) a).mpr ⟨rfl, by
    rw [hcint]; exact hrange⟩
  rw [hmin, hc]
  exact mul_div_cancel_left₀ _ hd0


#print axioms positiveRoster
#print axioms roster_units
#print axioms observations_decode_for_roster
#print axioms recover_literal_first_at_roster
end
end J8R59
