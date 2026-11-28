import J6R14SpecializedBoxRing
import J9R13ObservedChart

/-! Read the signed first coefficient once the actual receiving registers
have been identified. The sample prefix is exactly the printed binary
menu prefix, not an extra zero probe. This theorem is only a readout
adapter; its receipt equation must come from a physical execution. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial J8Physical J8EndToEnd J8J9Grouped NativeProbeRing DyadicProbeCompiler
open J9R13PhysicalFusion J9R13PhysicalTables LiteralPortCompiler J6R9Recursive
noncomputable section
set_option linter.unusedSectionVars false

theorem printed_probe_prefix (e N n : ℕ) (h : n≤N) (large : N≤2^e) (small : n≤2^e)
    (i : Fin n) :
    chosenRep e N large (Fin.castLE h i) = chosenRep e n small i := rfl

variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v,Fintype (P v)]

set_option maxHeartbeats 2200000 in
theorem signed_first_from_verified_receipts
    (e : EndpointSeating d) (he : Even L) (hL : 3≤L) (a : ℕ) (hpow : L=2^a)
    (s : S) (off : d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (idx : Wire R≃Fin M) (hCube : L^3≤M) (capacity : L*Fintype.card Packet≤3*M)
    (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (n : Fin (Fintype.card (PinTile d s))) (kt : TargetPorts d s→Source[X])
    (rows : (Fin M→Bool)→R→Bool→ℚ[X]) (cross : Fin L→ℚ[X]) (source : (Fin M→Bool)→ℚ[X])
    (q ell : ℕ) (hpq : 10*M≤q) (hℓ : 0<ell) (f : ℤ[X]) (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (residuePoly f))] (fit : 10*M+1≤2^f.natDegree)
    (received : Fin (10*M+1)→Box f ell q)
    (hReceived : ∀ i, received i = J6ActiveInterpolation.scalarIn q f ell
      (highObservation d e he (by omega) s F sign tail n kt a q f
        (chosenRep f.natDegree (10*M+1) fit i))) :
    let chart := J9End.chart d s idx (satisfied (globalCNF d idx F sign))
    let x := fun i => probe (10*M) f (chosenRep f.natDegree (10*M+1) fit i)
    let y := fun i => reduceScalar (10*M) q hpq f (atZero q f ell hℓ (received i))
    ((projectBase (10*M) f hf ((J9FactorBounds.publicDenominator chart n:Scalar (10*M) f) *
      NativeInterpolation.decode x y ⟨1, by
        have hM : 0<M := (show 0<L^3 by positivity).trans_le hCube
        omega⟩)).valMinAbs:ℚ) / J9FactorBounds.publicDenominator chart n =
      (J9End.literalCompleted chart n rows cross source).coeff 1 := by
  dsimp only
  simp_rw [hReceived,atZero_scalarIn]
  exact J9R13ObservedChart.read_chart_from_same_children d e he hL a hpow s off idx hCube capacity
    F sign tail n kt rows cross source q hpq f hf hd fit

#print axioms printed_probe_prefix
#print axioms signed_first_from_verified_receipts
end
end J6R14SpecializedBox