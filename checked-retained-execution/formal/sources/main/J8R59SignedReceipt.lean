import J6R14SpecializedBoxRing
import J8R59ReadChart

/-! Signed decoding of actual completed receiving registers for an arbitrary preselected legal binary roster. -/
namespace J8R59
open scoped Polynomial BigOperators Classical
open Polynomial J8Physical J8EndToEnd J8J9Grouped NativeProbeRing DyadicProbeCompiler
open J6R14SpecializedBox J9R13PhysicalFusion J9R13PhysicalTables LiteralPortCompiler J6R9Recursive
noncomputable section
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v,Fintype (P v)]

set_option maxHeartbeats 2200000 in
theorem signed_first_from_arbitrary_receipts
    (e : EndpointSeating d) (he : Even L) (hL : 3≤L) (a : ℕ) (hpow : L=2^a)
    (s : S) (off : d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (idx : Wire R≃Fin M) (hCube : L^3≤M) (capacity : L*Fintype.card Packet≤3*M)
    (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (n : Fin (Fintype.card (PinTile d s))) (kt : TargetPorts d s→Source[X])
    (rows : (Fin M→Bool)→R→Bool→ℚ[X]) (cross : Fin L→ℚ[X]) (source : (Fin M→Bool)→ℚ[X])
    (q ell : ℕ) (hpq : 10*M≤q) (hℓ : 0<ell) (f : ℤ[X]) (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (residuePoly f))] (W : Roster f (Fin (10*M+1)))
    (received : Fin (10*M+1)→Box f ell q)
    (hReceived : ∀ i, received i = J6ActiveInterpolation.scalarIn q f ell
      (highObservation d e he (by omega) s F sign tail n kt a q f
        (W i))) :
    let chart := J9End.chart d s idx (satisfied (globalCNF d idx F sign))
    let x := fun i => probe (10*M) f (W i)
    let y := fun i => reduceScalar (10*M) q hpq f (atZero q f ell hℓ (received i))
    ((projectBase (10*M) f hf ((J9FactorBounds.publicDenominator chart n:Scalar (10*M) f) *
      NativeInterpolation.decode x y ⟨1, by
        have hM : 0<M := (show 0<L^3 by positivity).trans_le hCube
        omega⟩)).valMinAbs:ℚ) / J9FactorBounds.publicDenominator chart n =
      (J9End.literalCompleted chart n rows cross source).coeff 1 := by
  dsimp only
  simp_rw [hReceived,atZero_scalarIn]
  exact read_chart_at_arbitrary_roster d e he hL a hpow s off idx hCube capacity
    F sign tail n kt rows cross source q hpq f hf hd W

def publicCoefficientAtRoster
    (s : S) (idx : Wire R≃Fin M) (n : Fin (Fintype.card (PinTile d s)))
    (q ell : ℕ) (hpq : 10*M≤q) (hℓ : 0<ell)
    (f : ℤ[X]) (hf : f.Monic) (W : Roster f (Fin (10*M+1))) (hM : 0<M)
    (received : Fin (10*M+1)→Box f ell q) : ℚ :=
  let U := J9FactorBounds.publicDenominator (J9End.chart d s idx (fun _ => false)) n
  let x := fun i => probe (10*M) f (W i)
  let y := fun i => reduceScalar (10*M) q hpq f (atZero q f ell hℓ (received i))
  ((projectBase (10*M) f hf ((U:Scalar (10*M) f) *
    NativeInterpolation.decode x y ⟨1,by omega⟩)).valMinAbs : ℚ) / U

/-- The same arithmetic readout for any table truth predicate. The
private input signs are not used to choose a scale or clearing factor. -/
theorem publicCoefficientAtRoster_exact_formula
    (s : S) (idx : Wire R≃Fin M) (n : Fin (Fintype.card (PinTile d s)))
    (q ell : ℕ) (hpq : 10*M≤q) (hℓ : 0<ell)
    (f : ℤ[X]) (hf : f.Monic) (W : Roster f (Fin (10*M+1))) (hM : 0<M)
    (received : Fin (10*M+1)→Box f ell q) (t : (Fin M→Bool)→Bool) :
    publicCoefficientAtRoster d s idx n q ell hpq hℓ f hf W hM received =
      let U := J9FactorBounds.publicDenominator (J9End.chart d s idx t) n
      let x := fun i => probe (10*M) f (W i)
      let y := fun i => reduceScalar (10*M) q hpq f (atZero q f ell hℓ (received i))
      ((projectBase (10*M) f hf ((U:Scalar (10*M) f) *
        NativeInterpolation.decode x y ⟨1,by omega⟩)).valMinAbs : ℚ) / U := rfl

#print axioms publicCoefficientAtRoster_exact_formula
#print axioms signed_first_from_arbitrary_receipts
end
end J8R59