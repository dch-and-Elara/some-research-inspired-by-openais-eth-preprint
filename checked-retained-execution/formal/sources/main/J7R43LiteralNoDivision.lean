import J7R43LiteralMass

/-! The division-free evaluator actually used by J7. All terms are
ordinary integers; each marginal accesses only its original bounded
column table. The only nonpublic entries are the original unary pins. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open J8Physical J8J9Grouped J8EndToEnd NativeChildRealization
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type} {P : V→Type} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
variable (e : EndpointSeating d) (even : Even L) (hL : 0<L)
variable (F : OldTables d) (sign : S→Bool)

def integerOldWeight (g : G) (v : LocalColumn d g) (z : LocalPort d v→Bool) : ℤ :=
  let W := groupWiring d e even g
  (LiteralPortCompiler.truth (F g v) z : ℤ) *
    ∏ r : {r : LocalRow d g // W.dest r = some v},
      (1 - J9FactorBounds.kernel L * J8J9Grouped.bit (z (W.port r.val v r.prop)))

def integerLocalMass (g : G) (v : LocalColumn d g) : ℤ :=
  ∑ z : LocalPort d v → Bool, integerOldWeight d e even F g v z

def integerBaseline (g : G) : ℤ :=
  ∏ v : LocalColumn d g, integerLocalMass d e even F g v

def integerMarginal (s : S) (y : OldTile d s) : ℤ :=
  let v := (tileOldInSource d y).1
  ∑ z : LocalPort d v→Bool,
    integerOldWeight d e even F (d.pinLabel s) v z *
      J8J9Grouped.bit (z (tileOldInSource d y).2)

def integerPinMoment (s : S) (b : ℕ) : ℤ :=
  ∑ j : Fin (Fintype.card (PinTile d s)),
    (ordinal d (pinWire d (pinEnumeration d s j).val) : ℤ)^b *
      J8J9Grouped.bit (sign (pinEnumeration d s j).val)

def integerSourceEvaluation (s : S) (b : ℕ) : ℤ :=
  (∑ y : OldTile d s, (ordinal d (ordinaryWire d y.val) : ℤ)^b * integerMarginal d e even F s y *
    ∏ v ∈ (Finset.univ : Finset (LocalColumn d (d.pinLabel s))).erase (tileOldInSource d y).1,
      integerLocalMass d e even F (d.pinLabel s) v) +
    integerBaseline d e even F (d.pinLabel s) * integerPinMoment d sign s b

theorem integer_bit_rat (x : Bool) : (J8J9Grouped.bit x : ℚ) = bitValue ℚ x := by
  cases x <;> simp [J8J9Grouped.bit,bitValue]

include hL in
theorem int_weight_rat (g : G) (v : LocalColumn d g) (z : LocalPort d v→Bool) :
    (integerOldWeight d e even F g v z : ℚ) =
      J8SourceMoment.localColumnWeight (groupWiring d e even g) (outerAmplitude L) (F g) none v z := by
  unfold integerOldWeight J8SourceMoment.localColumnWeight
  dsimp only
  rw [Int.cast_mul,Int.cast_prod]
  congr 1
  · exact LiteralPortCompiler.map_truth (Int.castRingHom ℚ) _ _
  · refine Finset.prod_congr rfl (fun r _ => ?_)
    rw [J8SourceMoment.localRow_formula]
    simp only [J8SourceMoment.marker,Option.bind_none,Int.cast_sub,Int.cast_one,Int.cast_mul,
      printed_amplitude_integral L hL even,integer_bit_rat]

include hL in
theorem int_mass_rat (g : G) (v : LocalColumn d g) :
    (integerLocalMass d e even F g v : ℚ) =
      mass (J8SourceMoment.localColumnWeight (groupWiring d e even g) (outerAmplitude L) (F g) none) v := by
  simp only [integerLocalMass,mass,Int.cast_sum,int_weight_rat d e even hL F]

include hL in
theorem int_baseline_rat (g : G) :
    (integerBaseline d e even F g : ℚ) = pinnedChildMass d e even F g := by
  simp only [integerBaseline,pinnedChildMass,Int.cast_prod,int_mass_rat d e even hL F]

include hL in
theorem literal_baseline_no_division (g : G) :
    J8J9Grouped.child d e even F sign g none (fun _ => 1) = integerBaseline d e even F g := by
  apply (Int.cast_injective : Function.Injective (fun n : ℤ => (n : ℚ)))
  rw [int_baseline_rat d e even hL F,actual_baseline_mass_formula d e even hL F sign]

include hL in
theorem local_marginal_no_division (s : S) (y : OldTile d s)
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F (d.pinLabel s) v) x = true) :
    let g := d.pinLabel s
    let wt := J8SourceMoment.localColumnWeight (groupWiring d e even g) (outerAmplitude L) (F g) none
    (integerMarginal d e even F s y : ℚ) *
      (∏ v ∈ (Finset.univ : Finset (LocalColumn d g)).erase (tileOldInSource d y).1, mass wt v) =
      pinnedChildMass d e even F g * mean wt (tileOldInSource d y).1
        (fun z => bitValue ℚ (z (tileOldInSource d y).2)) := by
  let g := d.pinLabel s
  let v := (tileOldInSource d y).1
  let wt := J8SourceMoment.localColumnWeight (groupWiring d e even g) (outerAmplitude L) (F g) none
  let num := (integerMarginal d e even F s y : ℚ)
  let den := mass wt v
  let tail := ∏ u ∈ (Finset.univ : Finset (LocalColumn d g)).erase v, mass wt u
  have hn : den ≠ 0 := (old_local_mass_positive d e even hL F g v (sat v)).ne'
  have hnum : num = ∑ z : LocalPort d v→Bool, wt v z * bitValue ℚ (z (tileOldInSource d y).2) := by
    simp only [num,integerMarginal,Int.cast_sum,Int.cast_mul, int_weight_rat d e even hL F,
      integer_bit_rat,wt,v,g]
  have hmass : pinnedChildMass d e even F g = den * tail := by
    unfold pinnedChildMass
    exact (Finset.mul_prod_erase (Finset.univ : Finset (LocalColumn d g)) (mass wt)
      (Finset.mem_univ v)).symm
  change num * tail = pinnedChildMass d e even F g * _
  rw [hmass]
  rw [mean, ← hnum]
  change num * tail = (den*tail)*(num/den)
  field_simp

theorem pin_part_rat (s : S) (b : Fin (Fintype.card (PinTile d s))) :
    (integerPinMoment d sign s b.val : ℚ) =
      NativeMomentReconstruction.moments (coordinates d s)
        (fun j => NativeMomentReconstruction.bitValue (sign (pinEnumeration d s j).val)) b := by
  unfold integerPinMoment NativeMomentReconstruction.moments coordinates
  simp only [Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [integer_bit_rat]
  cases (sign (pinEnumeration d s j).val) <;> simp [bitValue,NativeMomentReconstruction.bitValue]

set_option maxHeartbeats 3300000 in
include hL in
theorem literal_source_no_division (s : S) (b : Fin (Fintype.card (PinTile d s)))
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F (d.pinLabel s) v) x = true) :
    J8J9Grouped.child d e even F sign (d.pinLabel s) none (feature d s b) =
      integerSourceEvaluation d e even F sign s b.val := by
  apply (Int.cast_injective : Function.Injective (fun n : ℤ => (n : ℚ)))
  rw [actual_source_mass_formula d e even hL F sign s b sat]
  simp only [integerSourceEvaluation,Int.cast_add,Int.cast_sum,Int.cast_mul,Int.cast_prod,
    Int.cast_pow,Int.cast_natCast,int_baseline_rat d e even hL F,
    int_mass_rat d e even hL F,pin_part_rat d sign s b]
  rw [mul_add]
  congr 1
  unfold actualPublicMoment
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [mul_assoc,local_marginal_no_division d e even hL F s y sat]
  ac_rfl

#print axioms int_weight_rat
#print axioms int_mass_rat
#print axioms int_baseline_rat
#print axioms literal_baseline_no_division
#print axioms local_marginal_no_division
#print axioms pin_part_rat
#print axioms literal_source_no_division
end
end J7R43Literal