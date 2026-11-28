
import J9R19CompiledBitsLocal
import J9R19CompiledBitsFractions

/-! Exact integer pairs for the actual physical coefficient and both
public normalizers. Nonzero denominators use the original odd targets
and old-table positivity; no floating or rational inverse oracle. -/
namespace J9R19CompiledBits
open scoped BigOperators Classical
open J8Physical J8EndToEnd J8J9Grouped LiteralPortCompiler
noncomputable section
set_option linter.unusedSectionVars false

def unmatchedFactorZ (marked : Option Bool) : ℤ := if marked.isSome then -1 else 1

theorem unmatchedFactorZ_exact (marked : Option Bool) :
    (unmatchedFactorZ marked : ℚ) = J8SourceMoment.rowFactor marked 0 0 := by
  cases marked with
  | none => simp [unmatchedFactorZ,J8SourceMoment.rowFactor,J8SourceMoment.oldEquality_eq,TargetDerivative.equality]
  | some r => cases r <;> simp [unmatchedFactorZ,J8SourceMoment.rowFactor,J8SourceMoment.selectedEquality_eq]

variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

def groupIntMass (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (g : G) (mark : Option (LocalRow d g×Bool)) : ℤ :=
  (∏ r : {r : LocalRow d g // (groupWiring d e he g).dest r=none},
    unmatchedFactorZ (J8SourceMoment.marker mark r.1)) *
    ∏ v : LocalColumn d g,actualIntMass d e he F g mark v

theorem groupIntMass_exact (e : EndpointSeating d) (he : Even L) (hL : 1≤L)
    (F : OldTables d) (g : G) (mark : Option (LocalRow d g×Bool)) :
    (groupIntMass d e he F g mark : ℚ) = J9R18Compiled.groupMass d e he F g mark := by
  simp only [groupIntMass,Int.cast_mul,Int.cast_prod,unmatchedFactorZ_exact,
    actualIntMass_exact d e he hL,J9R18Compiled.groupMass,J8SourceMoment.unmatchedMultiplier]

theorem groupIntMass_fits (e : EndpointSeating d) (he : Even L) (hL : 1≤L)
    (F : OldTables d) (g : G) (mark : Option (LocalRow d g×Bool))
    (sparse : ∀ v, Fintype.card (P v)≤3) :
    Fits ((2*L+10)*Fintype.card V) (groupIntMass d e he F g mark) := by
  have w0 (p : Option Bool) : Fits 0 (unmatchedFactorZ p) := by
    cases p
    · simpa [unmatchedFactorZ] using Fits.one 0
    · simpa [unmatchedFactorZ] using (Fits.one 0).neg
  have h := fprod_fits Finset.univ (fun r : {r : LocalRow d g // (groupWiring d e he g).dest r=none} =>
    unmatchedFactorZ (J8SourceMoment.marker mark r.val)) (fun r _ => w0 _)
  have h' := fprod_fits Finset.univ (actualIntMass d e he F g mark) (fun v _ =>
    actualIntMass_fits d e he hL F g mark v (sparse v.val))
  have hc : Fintype.card (LocalColumn d g)≤ Fintype.card V :=
    Fintype.card_le_of_injective (f:=Subtype.val) Subtype.val_injective
  have h'' := (h.mul h').mono (by
    simp only [Nat.zero_mul,Nat.zero_add,Finset.card_univ]
    exact Nat.mul_le_mul_left _ hc)
  exact h''

def oldIntMoment (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (g : G) (q : Sigma (LocalPort d (g:=g))) : ℤ :=
  (∑ z : LocalPort d q.1→Bool, actualIntWeight d e he F g none q.1 z * bitZ (z q.2)) *
    ∏ v∈(Finset.univ : Finset (LocalColumn d g)).erase q.1,actualIntMass d e he F g none v

theorem oldIntMoment_exact (e : EndpointSeating d) (he : Even L) (hL : 1≤L)
    (F : OldTables d) (g : G) (q : Sigma (LocalPort d (g:=g))) :
    (oldIntMoment d e he F g q : ℚ) = J9R18Compiled.oldPortMoment d e he F g q := by
  simp only [oldIntMoment,Int.cast_mul,Int.cast_sum,Int.cast_prod,actualIntWeight_exact d e he hL,
    bitZ_cast,actualIntMass_exact d e he hL,J9R18Compiled.oldPortMoment,J9R18Compiled.oneColumn,
    J9R18Compiled.massAt]

def backgroundInt (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S) (b : ℕ) : ℤ :=
  ∑ q : OldTile d a, (ordinal d (ordinaryWire d q.1) : ℤ)^b *
    oldIntMoment d e he F (d.pinLabel a) (tileOldInSource d q)

theorem backgroundInt_exact (e : EndpointSeating d) (he : Even L) (hL : 1≤L)
    (F : OldTables d) (a : S) (b : ℕ) :
    (backgroundInt d e he F a b : ℚ) = J9R18Compiled.backgroundNumber d e he F a b := by
  simp only [backgroundInt,Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_natCast,
    oldIntMoment_exact d e he hL,J9R18Compiled.backgroundNumber]

def coordinateInt (a : S) (j : Fin (Fintype.card (PinTile d a))) : ℤ :=
  ordinal d (pinWire d (pinEnumeration d a j).1)

theorem coordinateInt_exact (a : S) (j : Fin (Fintype.card (PinTile d a))) :
    (coordinateInt d a j : ℚ)=coordinates d a j := by
  simp only [coordinateInt,coordinates,Int.cast_natCast]

theorem coordinateInt_injective (a : S) : Function.Injective (coordinateInt d a) := by
  intro i j h
  apply coordinates_injective d a
  simp only [← coordinateInt_exact, h]

def pinMomentZ (a : S) (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool) : ℤ :=
  ∑ i : Fin (Fintype.card (PinTile d a)),
    bitZ (sign (pinEnumeration d a i).1) * (coordinateInt d a i)^(b:ℕ)

theorem pinMomentZ_exact (a : S) (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool) :
    (pinMomentZ d a b sign : ℚ) = J9R18Compiled.pinMoment d a b sign := by
  simp only [pinMomentZ, J9R18Compiled.pinMoment,Int.cast_sum,Int.cast_mul,Int.cast_pow,
    bitZ_cast,coordinateInt_exact]
  rfl

def siblingsZ (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S) : ℤ :=
  ∏ g∈((Finset.univ : Finset G).erase (d.pinLabel a)).erase (d.rowLabel (pinWire d a).1),
    groupIntMass d e he F g none

theorem siblingsZ_exact (e : EndpointSeating d) (he : Even L) (hL : 1≤L)
    (F : OldTables d) (a : S) :
    (siblingsZ d e he F a : ℚ) = J9R18Compiled.siblingMass d e he F a := by
  simp only [siblingsZ,Int.cast_prod,groupIntMass_exact d e he hL,J9R18Compiled.siblingMass]

def targetFraction (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S)
    (b : ℕ) (j : TargetPorts d a) : Fraction :=
  ⟨J9FactorBounds.slope L b * groupIntMass d e he F (d.rowLabel (pinWire d a).1) (some j),
   (integerDenominator d a j)^(b+1)⟩

theorem targetFraction_exact (e : EndpointSeating d) (he : Even L) (hL : 1≤L)
    (F : OldTables d) (a : S) (b : ℕ) (j : TargetPorts d a) :
    (targetFraction d e he F a b j).value =
      J8SourceMoment.exactSlope (outerAmplitude L) (2*(L:ℚ)) (physicalDenominator d a j) b *
        J9R18Compiled.groupMass d e he F (d.rowLabel (pinWire d a).1) (some j) := by
  unfold targetFraction Fraction.value J9FactorBounds.slope J8SourceMoment.exactSlope
  push_cast
  rw [groupIntMass_exact d e he hL,printed_amplitude_integral L hL he,denominator_cast]
  rw [div_mul_eq_mul_div]

def targetClear (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S) (b : ℕ) : ClearRun :=
  clearRun ((groupedTargets d a).toList.map (targetFraction d e he F a b))

theorem targetClear_exact (e : EndpointSeating d) (he : Even L) (hL : 2<L)
    (F : OldTables d) (a : S) (b : ℕ) :
    (targetClear d e he F a b).result.value = J9R18Compiled.targetSlopeSum d e he F a b := by
  let targets := groupedTargets d a
  have hgood : ∀ f∈targets.toList.map (targetFraction d e he F a b), f.good := by
    intro f hf
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hf
    have hj' : j∈groupedTargets d a := by simpa [targets] using hj
    exact pow_ne_zero _ (groupedTargets_denom d a he hL hj').1.ne'
  change (clearRun (targets.toList.map (targetFraction d e he F a b))).result.value = _
  rw [clearRun_exact _ hgood,List.map_map]
  simp only [Function.comp_def,targetFraction_exact d e he (by omega)]
  unfold J9R18Compiled.targetSlopeSum
  let r (x : TargetPorts d a) :=
    J8SourceMoment.exactSlope (outerAmplitude L) (2*(L:ℚ)) (physicalDenominator d a x) b *
      J9R18Compiled.groupMass d e he F (d.rowLabel (pinWire d a).1) (some x)
  have eq := (List.sum_toFinset r targets.nodup_toList).symm
  rw [Finset.toList_toFinset] at eq
  exact eq

structure PhysicalFractions where
  first : Fraction
  scale : Fraction
  background : Fraction

def physicalFractions (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (a : S) (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool) : PhysicalFractions :=
  let src := groupIntMass d e he F (d.pinLabel a) none
  let bg := backgroundInt d e he F a b
  let sib := siblingsZ d e he F a
  let tgt := (targetClear d e he F a b).result
  let srcRead := bg + src*pinMomentZ d a b sign
  ⟨tgt.byInteger (sib*srcRead),tgt.byInteger (sib*src),⟨bg,src⟩⟩

theorem physicalFractions_exact (e : EndpointSeating d) (he : Even L) (hL : 2<L) (F : OldTables d)
    (a : S) (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool) :
    let q := physicalFractions d e he F a b sign
    q.first.value=J9R18Compiled.firstCoefficient d e he F a b sign ∧
    q.scale.value=J9R18Compiled.scale d e he F a b ∧
    q.background.value=J9R18Compiled.background d e he F a b := by
  dsimp only [physicalFractions]
  have hp : 1≤L := by omega
  refine ⟨?_,?_,?_⟩
  · simp only [Fraction.byInteger_exact,Int.cast_mul,Int.cast_add,groupIntMass_exact d e he hp,
      backgroundInt_exact d e he hp,pinMomentZ_exact,siblingsZ_exact d e he hp,
      targetClear_exact d e he hL,J9R18Compiled.firstCoefficient,J9R18Compiled.sourceMoment]
    ring
  · simp only [Fraction.byInteger_exact,Int.cast_mul,groupIntMass_exact d e he hp,
      siblingsZ_exact d e he hp,targetClear_exact d e he hL,J9R18Compiled.scale]
    ring
  · simp only [Fraction.value,J9R18Compiled.background,backgroundInt_exact d e he hp,
      groupIntMass_exact d e he hp]

#print axioms groupIntMass_exact
#print axioms groupIntMass_fits
#print axioms oldIntMoment_exact
#print axioms coordinateInt_injective
#print axioms targetFraction_exact
#print axioms targetClear_exact
#print axioms physicalFractions_exact

end
end J9R19CompiledBits
