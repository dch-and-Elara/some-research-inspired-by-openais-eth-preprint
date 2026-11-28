import J9R17AllPinsTile
import J9R17AllPinsAtlas
import J6R16SpecializedBoxReadReceipt

/-! Both stages of the decoder use public data only: the first
coefficient uses a structural odd denominator, and the final moment
recovery uses sign-free scale and background. -/
namespace J9R17AllPins
open scoped Polynomial BigOperators Classical
open Polynomial J8Physical J8EndToEnd J8J9Grouped NativeProbeRing LiteralPortCompiler
open J6R9Recursive J6R14SpecializedBox
noncomputable section
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

theorem clearingDenominator_public (s : S) (idx : Wire R≃Fin M)
    (t t' : (Fin M→Bool)→Bool) (n : ℕ) :
    J9FactorBounds.publicDenominator (J9End.chart d s idx t) n =
      J9FactorBounds.publicDenominator (J9End.chart d s idx t') n := rfl

def publicCoefficient
    (s : S) (idx : Wire R≃Fin M) (n : Fin (Fintype.card (PinTile d s)))
    (q ell : ℕ) (hpq : 10*M≤q) (hℓ : 0<ell)
    (f : ℤ[X]) (hf : f.Monic) (fit : 10*M+1≤2^f.natDegree) (hM : 0<M)
    (received : Fin (10*M+1)→Box f ell q) : ℚ :=
  let U := J9FactorBounds.publicDenominator (J9End.chart d s idx (fun _ => false)) n
  let x := fun i => probe (10*M) f (chosenRep f.natDegree (10*M+1) fit i)
  let y := fun i => reduceScalar (10*M) q hpq f (atZero q f ell hℓ (received i))
  ((projectBase (10*M) f hf ((U:Scalar (10*M) f) *
    NativeInterpolation.decode x y ⟨1,by omega⟩)).valMinAbs : ℚ) / U

/-- The same arithmetic readout for any table truth predicate. The
private input signs are not used to choose a scale or clearing factor. -/
theorem publicCoefficient_exact_formula
    (s : S) (idx : Wire R≃Fin M) (n : Fin (Fintype.card (PinTile d s)))
    (q ell : ℕ) (hpq : 10*M≤q) (hℓ : 0<ell)
    (f : ℤ[X]) (hf : f.Monic) (fit : 10*M+1≤2^f.natDegree) (hM : 0<M)
    (received : Fin (10*M+1)→Box f ell q) (t : (Fin M→Bool)→Bool) :
    publicCoefficient d s idx n q ell hpq hℓ f hf fit hM received =
      let U := J9FactorBounds.publicDenominator (J9End.chart d s idx t) n
      let x := fun i => probe (10*M) f (chosenRep f.natDegree (10*M+1) fit i)
      let y := fun i => reduceScalar (10*M) q hpq f (atZero q f ell hℓ (received i))
      ((projectBase (10*M) f hf ((U:Scalar (10*M) f) *
        NativeInterpolation.decode x y ⟨1,by omega⟩)).valMinAbs : ℚ) / U := rfl

def publicAllPinDecoder (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (obs : Orders d→ℚ) : S→Bool :=
  fun s =>
    let j := (orderPin d).symm s
    tileSignReadout d e he (anchor d j.1) F (fun _ => false) (fun _ _ _ _ => 0)
      (fun n => obs ⟨j.1,n⟩) j.2

theorem publicAllPinDecoder_exact
    (e : EndpointSeating d) (he : Even L) (hL : 2<L) (F : OldTables d) (sign : S→Bool)
    (off : ∀ s, d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (sat : ∀ g v, ∃ x, satisfied (F g v) x=true)
    (obs : Orders d→ℚ)
    (hObs : ∀ w : Orders d, obs w =
      physicalCoeff d e he (anchor d w.1) F sign (fun _ _ _ _ => 0) w.2 (fun _ => 0)) :
    publicAllPinDecoder d e he F obs = sign := by
  unfold publicAllPinDecoder
  refine gather_all_bits d (fun k => tileSignReadout d e he (anchor d k) F
    (fun _ => false) (fun _ _ _ _ => 0) (fun n => obs ⟨k,n⟩)) sign ?_
  intro k i
  exact congrFun (exact_physical_tile_from_receipts d e he hL (anchor d k) (off _) F sign sat
    (fun n => obs ⟨k,n⟩) (fun n => hObs ⟨k,n⟩)) i

#print axioms clearingDenominator_public
#print axioms publicCoefficient_exact_formula
#print axioms publicAllPinDecoder_exact
end
end J9R17AllPins