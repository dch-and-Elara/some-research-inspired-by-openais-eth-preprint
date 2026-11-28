
import J9R18CompiledChild

/-! A joint first-coefficient algorithm, and the exact same Vandermonde
decoder with its public constants compiled by local old-table sums. -/
namespace J9R18Compiled
open scoped Polynomial BigOperators Classical
open Polynomial J8Physical J8J9Grouped J8EndToEnd LiteralPortCompiler DyadicProbeCompiler
noncomputable section
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

def siblingMass (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S) : ℚ :=
  ∏ g ∈ ((Finset.univ : Finset G).erase (d.pinLabel a)).erase (d.rowLabel (pinWire d a).1),
    groupMass d e he F g none

theorem siblingMass_exact (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (a : S) (sign : S→Bool) (higher : RestArguments d) :
    siblingMass d e he F a = (publicSiblings d e he a F higher sign).coeff 0 := by
  simp only [siblingMass,publicSiblings,Polynomial.coeff_zero_prod,groupMass_exact,physicalMarked_constant]

/-- Sum only over the genuine target row ports of the one physical tile. -/
def targetSlopeSum (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S) (b : ℕ) : ℚ :=
  ∑ j ∈ groupedTargets d a,
    J8SourceMoment.exactSlope (outerAmplitude L) (2*(L:ℚ)) (physicalDenominator d a j) b *
      groupMass d e he F (d.rowLabel (pinWire d a).1) (some j)

def firstCoefficient (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (a : S) (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool) : ℚ :=
  (siblingMass d e he F a * targetSlopeSum d e he F a b) * sourceMoment d e he F a b sign

/-- No local satisfiability or positivity is needed for the evaluator
itself. It computes the original first coefficient even if that coefficient
vanishes. No higher probe terms are read and no separate slot is produced. -/
theorem firstCoefficient_exact (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (a : S) (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool)
    (higher : RestArguments d) (rest : TargetPorts d a→ℚ[X]) :
    firstCoefficient d e he F a b sign = physicalCoeff d e he a F sign higher b rest := by
  unfold physicalCoeff J8SourceMoment.completedTile NativeCompletedRecovery.completed
  dsimp only
  rw [TargetDerivative.first_completed_target _ _ _ _ _ (fun j _ =>
    J8SourceMoment.outerKernel_zero _ _ _ _ _)]
  simp only [J8SourceMoment.outerKernel_first,physicalMarked_constant,firstCoefficient,
    siblingMass_exact d e he F a sign higher, sourceMoment_exact d e he F a b sign higher,
    targetSlopeSum,groupMass_exact]
  rfl

set_option maxHeartbeats 2100000 in
/-- Same pinned source and exact structural output as the R13 literal
first-coefficient chart. Arbitrary tails are erased by the first read. -/
theorem firstCoefficient_is_literal (e : EndpointSeating d) (he : Even L) (hL : 2<L)
    (k : ℕ) (hpow : L=2^k) (F : OldTables d) (a : S)
    (off : d.rowLabel (pinWire d a).1≠d.pinLabel a) (idx : Wire R≃Fin M)
    (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool)
    (tail : IntegralArguments d) (kt : TargetPorts d a→Source[X])
    (rows : (Fin M→Bool)→R→Bool→ℚ[X]) (cross : Fin L→ℚ[X]) (s : (Fin M→Bool)→ℚ[X]) :
    firstCoefficient d e he F a b sign =
      (J9End.literalCompleted (J9End.chart d a idx
        (satisfied (J9R13PhysicalTables.globalCNF d idx F sign))) b rows cross s).coeff 1 :=
  (firstCoefficient_exact d e he F a b sign (fun _ _ _ _ => 0) (fun _ => 0)).trans
    (J9R17AllPins.chart_first_equals_physical_coeff d e he hL k hpow a off idx F sign
      tail (fun _ _ _ _ => 0) b kt (fun _ => 0) rows cross s).symm

def scale (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S) (b : ℕ) : ℚ :=
  (siblingMass d e he F a * targetSlopeSum d e he F a b) * groupMass d e he F (d.pinLabel a) none

theorem scale_exact (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (a : S) (b : ℕ) (sign : S→Bool) (higher : RestArguments d) :
    scale d e he F a b =
      J8SourceMoment.completedScale (publicSiblings d e he a F higher sign)
        (localChild d e he (d.pinLabel a) (outerAmplitude L) (F _))
        (localChild d e he (d.rowLabel (pinWire d a).1) (outerAmplitude L) (F _))
          (groupedTargets d a) (2*(L:ℚ)) (physicalDenominator d a) b := by
  simp only [scale,siblingMass_exact d e he F a sign higher,targetSlopeSum,groupMass_exact,
    J8SourceMoment.completedScale,J8SourceMoment.markedMass,J8SourceMoment.baselineMass]
  rfl

def background (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S) (b : ℕ) : ℚ :=
  backgroundNumber d e he F a b / groupMass d e he F (d.pinLabel a) none

theorem background_exact (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (a : S) (b : Fin (Fintype.card (PinTile d a))) :
    background d e he F a b =
      J8SourceMoment.nonpinBackground (localChild d e he (d.pinLabel a) (outerAmplitude L) (F _))
        (fun n => tileBackground d a n) b := by
  simp only [background,backgroundNumber_exact,groupMass_exact,J8SourceMoment.nonpinBackground,
    J8SourceMoment.baselineMass]

def readTile (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S)
    (obs : Fin (Fintype.card (PinTile d a))→ℚ) :
    Fin (Fintype.card (PinTile d a))→Bool :=
  NativeMomentReconstruction.decodeBits (coordinates d a)
    (fun n => scale d e he F a n) (fun n => background d e he F a n) obs

theorem readTile_exact (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S)
    (obs : Fin (Fintype.card (PinTile d a))→ℚ) :
    readTile d e he F a obs =
      tileSignReadout d e he a F (fun _ => false) (fun _ _ _ _ => 0) obs := by
  simp only [readTile, tileSignReadout,scale_exact d e he F _ _ (fun _ => false) (fun _ _ _ _ => 0),
    background_exact]

def readAll (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (obs : J9R17AllPins.Orders d→ℚ) : S→Bool := fun s =>
  let w := (J9R17AllPins.orderPin d).symm s
  readTile d e he F (J9R17AllPins.anchor d w.1) (fun n => obs ⟨w.1,n⟩) w.2

theorem readAll_exact (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (obs : J9R17AllPins.Orders d→ℚ) :
    readAll d e he F obs = J9R17AllPins.publicAllPinDecoder d e he F obs := by
  funext s
  unfold readAll J9R17AllPins.publicAllPinDecoder
  dsimp only
  rw [readTile_exact]

/-- All completed-order values and every public normalization are computed
locally; the last step is the same public Vandermonde inverse as R17. -/
theorem compiled_recovers_all (e : EndpointSeating d) (he : Even L) (hL : 2<L)
    (F : OldTables d) (sign : S→Bool)
    (off : ∀ s, d.rowLabel (pinWire d s).1≠d.pinLabel s)
    (sat : ∀ g v, ∃ x, satisfied (F g v) x=true) :
    readAll d e he F (fun w => firstCoefficient d e he F (J9R17AllPins.anchor d w.1) w.2 sign) =
      sign := by
  rw [readAll_exact]
  exact J9R17AllPins.publicAllPinDecoder_exact d e he hL F sign off sat _ fun w =>
    firstCoefficient_exact d e he F _ w.2 sign _ _

#print axioms siblingMass_exact
#print axioms firstCoefficient_exact
#print axioms firstCoefficient_is_literal
#print axioms scale_exact
#print axioms background_exact
#print axioms readTile_exact
#print axioms readAll_exact
#print axioms compiled_recovers_all

end
end J9R18Compiled
