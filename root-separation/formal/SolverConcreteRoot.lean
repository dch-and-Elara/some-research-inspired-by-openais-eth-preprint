import SolverRoot
import SolverValuation

noncomputable section
namespace RootSeparation.Solver
open Entry S11 GraphCutMoments Polynomial Classical

def RationalCoefficients {e : ℕ} (F : SourcePolynomial e) := RationalRing F.f

instance {e : ℕ} (F : SourcePolynomial e) : Field (RationalCoefficients F) := by
  let g := F.f.map (Int.castRingHom ℚ)
  letI : Fact (Irreducible g) := ⟨rational_irreducible F.monic F.irreducibleTwo⟩
  exact AdjoinRoot.instField (f := g)

instance {e : ℕ} (F : SourcePolynomial e) : CharZero (RationalCoefficients F) := by
  let g := F.f.map (Int.castRingHom ℚ)
  letI : Fact (Irreducible g) := ⟨rational_irreducible F.monic F.irreducibleTwo⟩
  change CharZero (AdjoinRoot g)
  exact algebraRat.charZero (R := AdjoinRoot g)

section Root

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (σ : V → Bool)
variable (F : SourcePolynomial (4*lambda (size E)))
variable (hn : bigRoot (n (V := V)))

abbrev RootSamples :=
  (t : RootCenter E) → RootProbe E → WordRing F.f (nativePrecision E t.val)

def tryRootWord (samples : RootSamples E F) :
    Option (WordRing F.f (initialPrecision (V := V))) :=
  tryWord F.monic (initialPrecision (V := V))
    (rootReadout (K := RationalCoefficients F) E reg F (integerRational F.f) hn samples)

def rootExactProbe (t : RootCenter E) (j : RootProbe E) : RationalCoefficients F :=
  let ζ : RationalCoefficients F := integerRational F.f (rootBinary E reg F hn j)
  let x : RationalCoefficients F := S7.scaledCenter (K := RationalCoefficients F) (rootA E) t.val
  eval (R := RationalCoefficients F) (x+ζ)
    (rootDeformation (K := RationalCoefficients F) E reg σ hn)

def rootProbeDifference (samples : RootSamples E F) (t : RootCenter E) (j : RootProbe E) :
    RationalRing F.f :=
  let y : RationalRing F.f := integerRational F.f
    (liftCanonical F.monic F.degree (Execution.nativePrecision_positive E t.val) (samples t j))
  let x : RationalRing F.f := rootExactProbe E reg σ F hn t j
  y-x

theorem tryRootWord_of_probe_congruence
    (huM : rootU E ≤ rootM E) (samples : RootSamples E F)
    (herr : ∀ (t : RootCenter E) (j : RootProbe E),
      (↑(nativePrecision E t.val:ℤ) : WithTop ℤ) ≤
      rationalValuation F (rootProbeDifference E reg σ F hn samples t j)) :
    tryRootWord E reg F hn samples =
      some (PinnedCNF.modelCount (PinnedCNF.formula E σ) : WordRing F.f (initialPrecision (V := V))) := by
  have hunit (i j : RootProbe E) (hij : i ≠ j) :
      rationalValuation F (integerRational F.f (rootBinary E reg F hn i) -
        integerRational F.f (rootBinary E reg F hn j)) = 0 :=
    binaryPoint_valuation_unit F _ _ (fun h => hij ((probe E reg hn).injective h))
  let v : AddValuation (RationalCoefficients F) (WithTop ℤ) := rationalValuation F
  let embed : IntegerRing F.f →+* RationalCoefficients F := integerRational F.f
  have hv : v 2 = 1 := rationalValuation_two F
  obtain ⟨err,he,hr⟩ := rootReadout_error (K := RationalCoefficients F) E reg σ F embed hn v hv
    (fun _ => rationalValuation_integer F _) hunit huM samples herr
  obtain ⟨err₀,herr₀⟩ := (coordinateOrder_nonnegative F.monic F.degree err).1 he
  unfold tryRootWord
  rw [hr, ← herr₀]
  let m := PinnedCNF.modelCount (PinnedCNF.formula E σ)
  change tryWord F.monic (initialPrecision (V := V))
    ((m : RationalRing F.f) + (2 : RationalRing F.f)^(initialPrecision (V := V)) *
      integralRational F.f err₀) = some (m : WordRing F.f (initialPrecision (V := V)))
  have hm : (m : RationalRing F.f) = integerRational F.f (m : IntegerRing F.f) :=
    (map_natCast (integerRational F.f) m).symm
  rw [hm,tryWord_error,map_natCast]

theorem tryRootWord_of_probe_residues (samples : RootSamples E F)
    (hsample : ∀ (t : RootCenter E) (j : RootProbe E),
      tryWord F.monic (nativePrecision E t.val) (rootExactProbe E reg σ F hn t j) =
        some (samples t j)) :
    tryRootWord E reg F hn samples =
      some (PinnedCNF.modelCount (PinnedCNF.formula E σ) : WordRing F.f (initialPrecision (V := V))) := by
  have hm : rootM E = 10 * n (V := V) := wire_count E reg
  have hs := (dimensions E reg).2
  have h : rootU E ≤ rootM E := (root_numeric (root_lambda E hn)
    (M := rootM E) (by omega) (by omega)).2.1
  apply tryRootWord_of_probe_congruence E reg σ F hn h samples
  intro t j
  exact canonical_probe_error F.monic F.degree _ (Execution.nativePrecision_positive E t.val)
    _ _ (hsample t j)

end Root

#print axioms tryRootWord
#print axioms tryRootWord_of_probe_congruence
#print axioms tryRootWord_of_probe_residues

end RootSeparation.Solver
