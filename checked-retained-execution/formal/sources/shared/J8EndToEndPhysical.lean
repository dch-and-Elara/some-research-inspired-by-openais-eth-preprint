import J8EndToEndBridge

/-!
One concrete packed J8 tile, from binary extension probes of the complete
product of compiled child sums to all of its pin signs. The residual
source assumptions are local constants and the cleared integer's size.
-/

namespace J8EndToEnd

open scoped Polynomial BigOperators Classical
open Polynomial NativeProbeRing DyadicProbeCompiler J8Physical

noncomputable section

variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

abbrev IntegralArguments :=
  (g : G) → ((LocalPin d g → Bool) × LocalBits d g) → LocalRow d g → Bool → Source[X]

def physicalTableWeight (F : OldTables d) (g : G) (x : LocalBits d g) : Source :=
  ∏ v : LocalColumn d g, LiteralPortCompiler.truth (F g v) (x v)

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [DecidableEq V] [Fintype G] [DecidableEq Packet] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem physicalWeight_agreement (e : EndpointSeating d) (even : Even L)
    (F : OldTables d) (g : G) (x : LocalBits d g) :
    rationalMap (physicalTableWeight d F g x) =
      (localChild d e even g (outerAmplitude L) (F g)).oldWeight x := by
  simp only [physicalTableWeight, map_prod, LiteralPortCompiler.map_truth, localChild,
    J8SourceMoment.literalChild]

def sourceBit (x : Bool) : Source := if x then 1 else 0

theorem sourceBit_agreement (b : Bool) :
    rationalMap (sourceBit b) = NativeMomentReconstruction.bitValue b := by
  cases b <;> simp [sourceBit, NativeMomentReconstruction.bitValue]

/-- Real old ports retain their true source addresses, and each real pin
also contributes with its actual slot index. The entire feature is integral. -/
def integralFeature (a : S) (b : Fin (Fintype.card (PinTile d a)))
    (x : (LocalPin d (d.pinLabel a) → Bool) × LocalBits d (d.pinLabel a)) : Source :=
  (∑ q : OldTile d a,
    (ordinal d (ordinaryWire d q.1) : Source)^(b : ℕ) *
      sourceBit (x.2 (tileOldInSource d q).1 (tileOldInSource d q).2)) +
  ∑ i : Fin (Fintype.card (PinTile d a)),
    sourceBit (x.1 (tilePinInSource d (pinEnumeration d a i))) *
      (ordinal d (pinWire d (pinEnumeration d a i).1) : Source)^(b : ℕ)

omit [Fintype R] [DecidableEq R] [DecidableEq S] [DecidableEq V] [Fintype G] [DecidableEq G] [(v : V) → DecidableEq (P v)] in
theorem feature_agreement (a : S) (b : Fin (Fintype.card (PinTile d a)))
    (x : (LocalPin d (d.pinLabel a) → Bool) × LocalBits d (d.pinLabel a)) :
    rationalMap (integralFeature d a b x) =
      J8SourceMoment.sourceFeature
        (fun i => tilePinInSource d (pinEnumeration d a i)) (coordinates d a)
          (fun j : Fin (Fintype.card (PinTile d a)) => tileBackground d a j) b x := by
  simp only [integralFeature, J8SourceMoment.sourceFeature, tileBackground, coordinates,
    map_add, map_sum, map_mul, map_pow, map_natCast, sourceBit_agreement]
  rfl

def liftedGroup (F : OldTables d) (base : IntegralArguments d) (sign : S → Bool) (g : G)
    (mark : Option (LocalRow d g × Bool)) (feature : ((LocalPin d g → Bool) × LocalBits d g) → Source) :
    Source[X] :=
  integralChild (physicalTableWeight d F g) (fun i : LocalPin d g => sign i.1)
    (base g) mark feature

def liftedPublic (a : S) (F : OldTables d) (base : IntegralArguments d) (sign : S → Bool) : Source[X] :=
  ∏ g ∈ ((Finset.univ : Finset G).erase (d.pinLabel a)).erase (d.rowLabel (pinWire d a).1),
    liftedGroup d F base sign g none (fun _ => 1)

def ArgsAgree (e : EndpointSeating d) (even : Even L)
    (F : OldTables d) (base : IntegralArguments d) : Prop :=
  ∀ g x r leg, rationalMap ((base g x r leg).coeff 0) =
    J8SourceMoment.input0 (localChild d e even g (outerAmplitude L) (F g)) x.2 r leg

omit [Fintype G] [DecidableEq Packet] in
theorem liftedGroup_matches (e : EndpointSeating d) (even : Even L) (F : OldTables d)
    (base : IntegralArguments d) (sign : S → Bool) (higher : RestArguments d)
    (agree : ArgsAgree d e even F base) (g : G) (mark : Option (LocalRow d g × Bool))
    (feat : ((LocalPin d g → Bool) × LocalBits d g) → Source)
    (rationalFeat : ((LocalPin d g → Bool) × LocalBits d g) → ℚ)
    (feat_eq : ∀ x, rationalMap (feat x) = rationalFeat x) :
    rationalMap ((liftedGroup d F base sign g mark feat).coeff 0) =
      (J8SourceMoment.genuineChild (localChild d e even g (outerAmplitude L) (F g))
        (fun i : LocalPin d g => sign i.1) (higher g) mark rationalFeat).coeff 0 :=
  child_const_matches _ _ _ _ _ _ _ _ (physicalWeight_agreement d e even F g) feat_eq (agree g)

omit [DecidableEq Packet] in
theorem liftedPublic_matches (e : EndpointSeating d) (even : Even L) (a : S) (F : OldTables d)
    (base : IntegralArguments d) (sign : S → Bool) (higher : RestArguments d)
    (agree : ArgsAgree d e even F base) :
    rationalMap ((liftedPublic d a F base sign).coeff 0) =
      (publicSiblings d e even a F higher sign).coeff 0 := by
  simp only [liftedPublic, publicSiblings, Polynomial.coeff_zero_prod, map_prod]
  exact Finset.prod_congr rfl (fun g _ =>
    liftedGroup_matches d e even F base sign higher agree g none _ _ (fun _ => map_one _))

/-- The actual native grouped sample readouts recover every pin of this
physical tile. Only the constant of each local base/kernel and the exact
cleared integer bound is required; no global agreement of samples or
whole coefficients is an input. Higher local terms are not constrained
by this first-coefficient theorem. -/
theorem recover_grouped_physical_tile
    (e : EndpointSeating d) (a : S) (even : Even L) (hL : 2 < L)
    (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a)
    (F : OldTables d) (base : IntegralArguments d) (sign : S → Bool) (higher : RestArguments d)
    (sat : ∀ g v, ∃ x, LiteralPortCompiler.satisfied (F g v) x = true)
    (agree : ArgsAgree d e even F base)
    (p : ℕ) (hp : 0 < p) (f : ℤ[X]) (hf : f.Monic) (hd : 0 < f.natDegree)
    [Fact (Irreducible (residuePoly f))]
    (addr : Fin (p+1) → Fin f.natDegree → Bool) (distinct : Function.Injective addr)
    (exponent : Fin (Fintype.card (PinTile d a)) → ℕ)
    (he : ∀ b, 1 ≤ exponent b)
    (targetTail : Fin (Fintype.card (PinTile d a)) → TargetPorts d a → ℚ[X])
    (kernel : Fin (Fintype.card (PinTile d a)) → TargetPorts d a → Source[X])
    (kernelConst : ∀ b j, j ∈ groupedTargets d a →
      (2:ℚ)^exponent b * rationalMap ((kernel b j).coeff 0) =
        J8SourceMoment.exactSlope (outerAmplitude L) (2*(L:ℚ))
          (physicalDenominator d a j) b)
    (clear num : Fin (Fintype.card (PinTile d a)) → ℤ)
    (hclear : ∀ b, clear b ≠ 0)
    (fits : ∀ b, num b*2 ∈ Set.Ioc (-(↑((2:ℕ)^p)) : ℤ) ↑((2:ℕ)^p)) :
    let gS := d.pinLabel a
    let gT := d.rowLabel (pinWire d a).1
    let s := groupedTargets d a
    let α := 2*(L:ℚ)
    let den := physicalDenominator d a
    let Sg := localChild d e even gS (outerAmplitude L) (F gS)
    let Tg := localChild d e even gT (outerAmplitude L) (F gT)
    let pub := publicSiblings d e even a F higher sign
    let loc := liftedPublic d a F base sign
    let sites := fun i => tilePinInSource d (pinEnumeration d a i)
    let other := fun b : Fin (Fintype.card (PinTile d a)) => tileBackground d a b
    let qS := fun b => liftedGroup d F base sign gS none (integralFeature d a b)
    let qT := fun j => liftedGroup d F base sign gT (some j) (fun _ => 1)
    let physical := fun b : Fin (Fintype.card (PinTile d a)) =>
      (J8SourceMoment.completedTile pub Sg Tg (fun i => sign i.1) (fun i => sign i.1)
        (higher gS) (higher gT) sites (coordinates d a) other s α den (targetTail b) b).coeff 1
    let obs := fun b : Fin (Fintype.card (PinTile d a)) =>
      let x := fun j => probe p f (addr j)
      readRational p f hf (clear b) (NativeInterpolation.decode x
        (fun j => groupedProbe p f (exponent b) s loc (qS b) qT (kernel b) (x j)) ⟨1,by omega⟩)
    (∀ b, (num b : ℚ) = clear b * physical b) →
      NativeMomentReconstruction.decodeBits (coordinates d a)
        (fun b => J8SourceMoment.completedScale pub Sg Tg s α den b)
        (J8SourceMoment.nonpinBackground Sg other) obs = fun i => sign (pinEnumeration d a i).1 := by
  dsimp only
  intro numerator
  have raw := J8Physical.recover_physical_tile_exact d e even a hL off F higher sign sat targetTail
  dsimp only at raw
  convert raw using 2
  funext b
  apply grouped_read_compares p hp f hf hd (exponent b) (he b) addr distinct
  · exact liftedPublic_matches d e even a F base sign higher agree
  · apply liftedGroup_matches d e even F base sign higher agree
    exact feature_agreement d a b
  · intro j hj
    exact liftedGroup_matches d e even F base sign higher agree _ _ _ _ (fun _ => map_one _)
  · intro j hj
    rw [J8SourceMoment.outerKernel_first]
    exact kernelConst b j hj
  · intro j hj
    exact J8SourceMoment.outerKernel_zero _ _ _ _ _
  · exact hclear b
  · exact fits b
  · exact numerator b

#print axioms physicalWeight_agreement
#print axioms feature_agreement
#print axioms liftedPublic_matches
#print axioms recover_grouped_physical_tile

end
end J8EndToEnd
