import SolverNativeRun

noncomputable section
namespace RootSeparation.Solver
open S11 Polynomial Classical
open scoped BigOperators

variable {s : ℕ} (F : SourcePolynomial (4*lambda s))
variable {c : Call F.f} (G : CallLayout s c)
variable (cap : probeCount c.edges (callL s c) ≤ 2^(4*lambda s))

def callDeformation : (RationalCoefficients F)[X] :=
  normalizedDeformation (K := RationalCoefficients F)
    (c.network.map (integerRational F.f)) G.packing.position

def exactCallProbe (t : callCenters s c) (j : callProbes s c) : RationalRing F.f :=
  let ζ : RationalCoefficients F := callPoint F cap j
  let x : RationalCoefficients F := S7.scaledCenter (K := RationalCoefficients F) (callA s c) t.val
  eval (R := RationalCoefficients F) (x+ζ) (callDeformation F G)

theorem callDeformation_origin :
    (callDeformation F G).eval 0 = integerRational F.f c.network.contract := by
  rw [callDeformation,normalizedDeformation_origin]
  exact Network.map_contract _ _

/-- Decoder correctness once the current probe residues are established.
    The children and their stored tables enter upstream of this lemma. -/
theorem recoverCall_of_probe_residues (hu : 0 < callU s c) (huM : callU s c ≤ c.edges)
    (samples : CallReturned F c)
    (h : ∀ (t : callCenters s c) (j : callProbes s c), tryWord F.monic (callPrecision s c t.val) (exactCallProbe F G cap t j) =
      some (samples t j)) :
    recoverCall F c cap samples = some (fromInteger F.f c.precision c.network.contract) := by
  let v : AddValuation (RationalCoefficients F) (WithTop ℤ) := rationalValuation F
  let embed : IntegerRing F.f →+* RationalCoefficients F := integerRational F.f
  have huA : 0 < callA s c := hu.trans_le G.u_le_a
  have hM : 0 < c.edges := (Nat.zero_le _).trans_lt G.positive
  have hp (i j : callProbes s c) (hne : i ≠ j) :
      v (callPoint F cap i - callPoint F cap j) = 0 :=
    binaryPoint_valuation_unit F _ _ (fun he => hne (binaryProbe_injective _ _ cap he))
  have hd := normalizedDeformation_window (K := RationalCoefficients F)
    (c.network.map embed) G.packing.position (callU s c) hM hu huA
  have hd' (t : callCenters s c) :
      ((callDeformation F G).comp (X+C (S7.scaledCenter (callA s c) t.val))).degree <
        ↑(Fintype.card (callProbes s c)) := by
    rw [Fintype.card_fin]
    exact normalizedDeformation_local (K := RationalCoefficients F)
      (c.network.map embed) G.packing.position t.val
  have hprec (t : callCenters s c) (j : callProbes s c) :
      (↑(callPrecision s c t.val:ℤ):WithTop ℤ) ≤ v
        (embed (liftCanonical F.monic F.degree (callPrecision_pos s c t.val) (samples t j)) -
          (callDeformation F G).eval (S7.scaledCenter (callA s c) t.val + callPoint F cap j)) :=
    canonical_probe_error F.monic F.degree _ (callPrecision_pos s c t.val) _ _ (h t j)
  obtain ⟨err,he,hr⟩ := recover_modular (J := callProbes s c) v (rationalValuation_two F)
    c.edges (callA s c) (callU s c) c.precision hM hu huM
    (fun _ j => callPoint F cap j) (fun _ _ => rationalValuation_integer F _)
      (fun _ => hp) (callDeformation F G) hd hd' _ hprec
  rw [callDeformation_origin] at hr
  obtain ⟨err₀,herr₀⟩ := (coordinateOrder_nonnegative F.monic F.degree err).1 he
  refine (congrArg (tryWord F.monic c.precision) hr).trans ?_
  change tryWord F.monic c.precision
    (integerRational F.f c.network.contract + (2:RationalRing F.f)^c.precision*(show RationalRing F.f from err)) = _
  rw [← herr₀]
  exact tryWord_error F.monic c.precision c.network.contract err₀

end RootSeparation.Solver

#print axioms RootSeparation.Solver.callDeformation_origin
#print axioms RootSeparation.Solver.recoverCall_of_probe_residues
