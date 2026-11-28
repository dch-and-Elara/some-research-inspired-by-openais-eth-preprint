import J8J9GroupedTerm
import J8EndToEndAmplitude

/-! J7, before taking a residue: the old bounded column tables give a
positive baseline mass and the literal integer moment is baseline times
the sum of the real pin and nonpin weighted bit means. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open Polynomial J8Physical J8J9Grouped J8EndToEnd DyadicProbeCompiler
open NativeChildRealization
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type} {P : V→Type} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
variable (e : EndpointSeating d) (even : Even L) (hL : 0<L)
variable (F : OldTables d) (sign : S→Bool)

def pinnedChildMass (g : G) : ℚ :=
  ∏ v : LocalColumn d g, mass
    (J8SourceMoment.localColumnWeight (groupWiring d e even g) (outerAmplitude L) (F g) none) v

def actualPublicMoment (s : S) (b : ℕ) : ℚ :=
  ∑ y : OldTile d s, (ordinal d (ordinaryWire d y.val) : ℚ)^b *
    mean (J8SourceMoment.localColumnWeight (groupWiring d e even (d.pinLabel s))
      (outerAmplitude L) (F (d.pinLabel s)) none) (tileOldInSource d y).1
      (fun z => bitValue ℚ (z (tileOldInSource d y).2))

include hL in
theorem old_local_mass_positive (g : G) (v : LocalColumn d g)
    (sat : ∃ x, LiteralPortCompiler.satisfied (F g v) x = true) :
    0 < mass (J8SourceMoment.localColumnWeight (groupWiring d e even g)
      (outerAmplitude L) (F g) none) v := by
  let W := groupWiring d e even g
  let c := outerAmplitude L
  have hc : c<0 := amplitude_negative L hL even
  have hpow (x : LocalPort d v → Bool) :
      0 < ∏ r : {r : LocalRow d g // W.dest r = some v}, J8SourceMoment.localRow none r.val
        (W.leg r.val) (c * bitValue ℚ (x (W.port r.val v r.prop))) := by
    refine Finset.prod_pos (fun r _ => ?_)
    rw [J8SourceMoment.localRow_formula]
    simp only [J8SourceMoment.marker,Option.bind_none]
    cases x (W.port r.val v r.prop)
    · simp [bitValue]
    · simp [bitValue]; linarith
  obtain ⟨x,hx⟩ := sat
  unfold mass
  refine Finset.sum_pos' (fun z _ => ?_) ⟨x,Finset.mem_univ _,?_⟩
  · unfold J8SourceMoment.localColumnWeight
    refine mul_nonneg ?_ (hpow z).le
    unfold LiteralPortCompiler.truth LiteralPortCompiler.indicator
    split_ifs <;> norm_num
  · unfold J8SourceMoment.localColumnWeight
    apply mul_pos _ (hpow x)
    simp [LiteralPortCompiler.truth,LiteralPortCompiler.indicator,hx]

include hL in
theorem all_local_mass_positive (g : G) (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F g v) x = true) :
    0 < pinnedChildMass d e even F g := by
  unfold pinnedChildMass
  exact Finset.prod_pos (fun v _ => old_local_mass_positive d e even hL F g v (sat v))

theorem weighted_baseline_is_local_mass (g : G) :
    J8SourceMoment.baselineMass (localChild d e even g (outerAmplitude L) (F g)) =
      pinnedChildMass d e even F g := by
  unfold J8SourceMoment.baselineMass localChild
  rw [J8SourceMoment.marked_mass_local, J8SourceMoment.unmatchedMultiplier_baseline, one_mul]
  rfl

include hL in
theorem grouped_argument_rational (g : G) (x : Assignment d g) (r : LocalRow d g) (leg : Bool) :
    (argument d e even g x r leg : ℚ) =
      J8SourceMoment.input0 (localChild d e even g (outerAmplitude L) (F g)) x.2 r leg := by
  let tail : IntegralArguments d := fun _ _ _ _ => 0
  have h := constructed_base_agrees d e even (J9FactorBounds.kernel L)
    (printed_amplitude_integral L hL even) F tail g x r leg
  rw [← argument_cast d e even tail g x r leg,map_intCast] at h
  exact h

set_option maxHeartbeats 2000000 in
include hL in
theorem physical_child_integer_as_rational (g : G) (feat : Assignment d g→ℤ) :
    (J8J9Grouped.child d e even F sign g none feat : ℚ) =
    (J8SourceMoment.genuineChild (localChild d e even g (outerAmplitude L) (F g))
      (fun q : LocalPin d g => sign q.val) (fun _ _ _ => 0) none (fun x => (feat x : ℚ))).coeff 0 := by
  let pinSign := fun q : LocalPin d g => sign q.val
  let child := localChild d e even g (outerAmplitude L) (F g)
  have cast_summand (x : LocalBits d g) (pins : LocalPin d g→Bool) :
      (summand d e even F sign g none feat (pins,x) : ℚ) =
        if pins=pinSign then J8SourceMoment.weighted child none x * (feat (pins,x) : ℚ)
          else 0 := by
    let q := (pins,x)
    let pinFactor : ℤ := ∏ pin : LocalPin d g,
      LiteralPortCompiler.truth (LiteralPortCompiler.pin pin (sign pin.val)) pins
    have hPin : (pinFactor : ℚ) = J8SourceMoment.pinWeight pinSign pins := by
      change (Int.castRingHom ℚ) (∏ pin : LocalPin d g, LiteralPortCompiler.truth
        (LiteralPortCompiler.pin pin (sign pin.val)) pins) = _
      rw [map_prod,J8SourceMoment.pinWeight]
      refine Finset.prod_congr rfl (fun pin _ => ?_)
      exact LiteralPortCompiler.map_truth (Int.castRingHom ℚ) _ _
    have hOld : (table d F g x : ℚ) = child.oldWeight x := by
      unfold table child localChild J8SourceMoment.literalChild
      rw [Int.cast_prod]
      refine Finset.prod_congr rfl (fun v _ => ?_)
      exact LiteralPortCompiler.map_truth (Int.castRingHom ℚ) _ _
    have hInput (r : LocalRow d g) (leg : Bool) :=
      grouped_argument_rational d e even hL F g q r leg
    unfold summand tablesAt
    simp only [Int.cast_mul]
    change (pinFactor : ℚ) * (table d F g x : ℚ) * (feat q : ℚ) * _ = _
    rw [hPin,hOld,J8SourceMoment.pinWeight_iff,J8SourceMoment.weighted,Int.cast_prod]
    have hCast (r : LocalRow d g) :
        ((J8SourceMoment.rowFactor (J8SourceMoment.marker none r)
          (argument d e even g (pins,x) r false) (argument d e even g (pins,x) r true) : ℤ) : ℚ) =
          J8SourceMoment.rowFactor (J8SourceMoment.marker none r)
            (J8SourceMoment.input0 child x r false) (J8SourceMoment.input0 child x r true) := by
      change (Int.castRingHom ℚ) (J8SourceMoment.rowFactor _ _ _) = _
      rw [J8SourceMoment.map_rowFactor]
      exact congrArg₂ (J8SourceMoment.rowFactor (J8SourceMoment.marker none r))
        (hInput r false) (hInput r true)
    by_cases hp : pins=pinSign
    · simp only [if_pos hp,one_mul,hCast]
      ac_rfl
    · simp only [if_neg hp,zero_mul]
  rw [child_as_sum,Int.cast_sum,Fintype.sum_prod_type,Finset.sum_comm,
    J8SourceMoment.childConstant]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [cast_summand,Fintype.sum_ite_eq']
  rfl
include hL in
theorem actual_baseline_mass_formula (g : G) :
    (J8J9Grouped.child d e even F sign g none (fun _ => 1) : ℚ) = pinnedChildMass d e even F g := by
  rw [physical_child_integer_as_rational d e even hL F sign]
  simp only [Int.cast_one, J8SourceMoment.childConstant, mul_one]
  exact weighted_baseline_is_local_mass d e even F g

include hL in
theorem local_public_mean_exact (s : S) (b : Fin (Fintype.card (PinTile d s)))
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F (d.pinLabel s) v) x = true) :
    J8SourceMoment.nonpinBackground (localChild d e even (d.pinLabel s) (outerAmplitude L)
      (F (d.pinLabel s))) (fun n : Fin (Fintype.card (PinTile d s)) => tileBackground d s n.val) b =
      actualPublicMoment d e even F s b.val := by
  let g := d.pinLabel s
  let wt := J8SourceMoment.localColumnWeight (groupWiring d e even g)
    (outerAmplitude L) (F g) none
  have hneu (v : LocalColumn d g) : mass wt v ≠ 0 :=
    (old_local_mass_positive d e even hL F g v (sat v)).ne'
  have h := J8SourceMoment.source_moment_local (groupWiring d e even g) (outerAmplitude L) (F g)
    (fun y : OldTile d s => tileOldInSource d y)
    (fun y => (ordinal d (ordinaryWire d y.val) : ℚ)^b.val) hneu
  have hm := all_local_mass_positive d e even hL F g sat
  unfold J8SourceMoment.nonpinBackground
  rw [weighted_baseline_is_local_mass]
  apply (div_eq_iff hm.ne').mpr
  have h' : _ = pinnedChildMass d e even F g * actualPublicMoment d e even F s b.val := h
  exact h'.trans (mul_comm _ _)

set_option maxHeartbeats 3600000 in
include hL in
theorem actual_source_mass_formula (s : S) (b : Fin (Fintype.card (PinTile d s)))
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F (d.pinLabel s) v) x = true) :
    (J8J9Grouped.child d e even F sign (d.pinLabel s) none (feature d s b) : ℚ) =
      pinnedChildMass d e even F (d.pinLabel s) *
      (actualPublicMoment d e even F s b.val + NativeMomentReconstruction.moments (coordinates d s)
        (fun j => NativeMomentReconstruction.bitValue (sign (pinEnumeration d s j).val)) b) := by
  rw [physical_child_integer_as_rational d e even hL F sign]
  have hfeat (x : Assignment d (d.pinLabel s)) :
      (feature d s b x : ℚ) = J8SourceMoment.sourceFeature
        (fun j => tilePinInSource d (pinEnumeration d s j)) (coordinates d s)
        (fun n : Fin (Fintype.card (PinTile d s)) => tileBackground d s n.val) b x := by
    have h := feature_agreement d s b x
    rwa [← feature_cast d s b x,map_intCast] at h
  simp_rw [hfeat]
  rw [J8SourceMoment.sourceConstant_exact]
  · rw [local_public_mean_exact d e even hL F s b sat,weighted_baseline_is_local_mass]
    rfl
  · rw [weighted_baseline_is_local_mass]
    exact (all_local_mass_positive d e even hL F _ sat).ne'

#print axioms old_local_mass_positive
#print axioms all_local_mass_positive
#print axioms weighted_baseline_is_local_mass
#print axioms grouped_argument_rational
#print axioms physical_child_integer_as_rational
#print axioms actual_baseline_mass_formula
#print axioms local_public_mean_exact
#print axioms actual_source_mass_formula
end
end J7R43Literal