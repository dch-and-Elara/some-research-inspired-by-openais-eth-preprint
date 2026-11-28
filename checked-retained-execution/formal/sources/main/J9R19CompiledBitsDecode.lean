
import J9R19CompiledBitsPhysical
import J9R19CompiledBitsWidths

/-! End-to-end integer comparison with the R18 compiled decoder. The
normalised fractions are stored once on a finite tape per recovered site,
and no division operation occurs even for its Boolean output. -/
namespace J9R19CompiledBits
open scoped BigOperators Classical
open J8Physical J8EndToEnd J8J9Grouped LiteralPortCompiler
set_option linter.unusedSectionVars false

def normalTape {n : ℕ} (q : Fin n→PhysicalFractions) : List NormalizeRun :=
  List.ofFn (fun j => let a := q j; normalizeRun a.first a.scale a.background)

def storedFraction (data : List NormalizeRun) (j : ℕ) : Fraction :=
  ((data[j]?).map NormalizeRun.result).getD ⟨0,1⟩

theorem stored_normal {n : ℕ} (q : Fin n→PhysicalFractions) (j : Fin n) :
    storedFraction (normalTape q) j.val =
      (normalizeRun (q j).first (q j).scale (q j).background).result := by
  simp [storedFraction,normalTape,j.isLt]

structure RecoveryRun where
  answer : Bool
  work : ℕ

def recoverRun {n : ℕ} (coord : Fin n → ℤ) (q : Fin n→PhysicalFractions) (i : Fin n) : RecoveryRun :=
  let norms := normalTape q
  let r := evaluateStencil coord (fun j => storedFraction norms j.val) i
  ⟨decide (r.result.num=r.result.den),(norms.map NormalizeRun.work).sum+r.work+1⟩

theorem recoverRun_work {n : ℕ} (coord : Fin n → ℤ) (q : Fin n→PhysicalFractions) (i : Fin n) :
    (recoverRun coord q i).work ≤ n*(n+1)+14*n+2 := by
  have hnorm : ((normalTape q).map NormalizeRun.work).sum = 6*n := by
    unfold normalTape
    rw [List.map_ofFn,List.sum_ofFn]
    simp [normalizeRun_total_work]
    omega
  have hw := evaluateStencil_work coord (fun j => storedFraction (normalTape q) j.val) i
  dsimp only [recoverRun]
  omega

theorem recoverRun_exact {n : ℕ} (coord : Fin n → ℤ) (q : Fin n→PhysicalFractions) (i : Fin n)
    (inj : Function.Injective coord) (good : ∀ j, (q j).first.good ∧
      (q j).scale.num≠0 ∧ (q j).background.good) :
    (recoverRun coord q i).answer =
      J9R18Compiled.stencilDecodeBits (fun j => (coord j:ℚ))
        (fun j => (q j).scale.value) (fun j => (q j).background.value)
        (fun j => (q j).first.value) i := by
  let v : Fin n→Fraction := fun j => storedFraction (normalTape q) j.val
  have hv (j : Fin n) : (v j).good := by
    dsimp [v]
    rw [stored_normal]
    exact normalizeRun_good _ _ _ (good j).1 (good j).2.1 (good j).2.2
  have val (j : Fin n) : (v j).value =
      (q j).first.value / (q j).scale.value - (q j).background.value := by
    dsimp [v]
    rw [stored_normal]
    exact normalizeRun_exact _ _ _ (good j).1 (good j).2.1 (good j).2.2
  let r := evaluateStencil coord v i
  have eq : r.result.num=r.result.den ↔
      J9R18Compiled.stencilInverse (fun j => (coord j:ℚ))
        (fun j => (q j).first.value / (q j).scale.value - (q j).background.value) i=1 := by
    rw [Fraction.testOne_exact _ (evaluateStencil_good coord v i inj hv),
      evaluateStencil_exact coord v i inj hv,funext val]
  change decide (r.result.num=r.result.den) = _
  unfold J9R18Compiled.stencilDecodeBits
  by_cases h : r.result.num=r.result.den
  · simp [h,eq.mp h]
  · have h' : ¬ J9R18Compiled.stencilInverse (fun j => (coord j:ℚ))
        (fun j => (q j).first.value / (q j).scale.value - (q j).background.value) i=1 :=
      fun he => h (eq.mpr he)
    simp [h,h']

noncomputable section
variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

theorem physicalFractions_good (e : EndpointSeating d) (he : Even L) (hL : 2<L) (F : OldTables d)
    (a : S) (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool)
    (off : d.rowLabel (pinWire d a).1≠d.pinLabel a)
    (sat : ∀ g v, ∃ z, satisfied (F g v) z=true) :
    let q := physicalFractions d e he F a b sign
    q.first.good ∧ q.scale.num≠0 ∧ q.background.good := by
  dsimp only
  have localSat := sat
  have hd : (targetClear d e he F a b).result.good := by
    unfold targetClear
    apply clearRun_good
    intro q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hq
    have hm : j∈groupedTargets d a := by simpa using hj
    exact pow_ne_zero _ (groupedTargets_denom d a he hL hm).1.ne'
  let amp := outerAmplitude L
  have hneg : amp<0 := amplitude_negative L (by omega) he
  have hs (g : G) : 0 < J8SourceMoment.baselineMass (localChild d e he g amp (F g)) :=
    J8SourceMoment.baselineMass_pos _ hneg (J8SourceMoment.old_nonnegative _ _ _)
      (J8SourceMoment.old_has_assignment _ _ _ (localSat g))
  have hsZ : groupIntMass d e he F (d.pinLabel a) none ≠ 0 := by
    intro h
    have hh := groupIntMass_exact d e he (by omega) F (d.pinLabel a) none
    rw [h,Int.cast_zero,J9R18Compiled.groupMass_exact] at hh
    exact (hs (d.pinLabel a)).ne' hh.symm
  have hscale : 0 < J9R18Compiled.scale d e he F a b := by
    rw [J9R18Compiled.scale_exact d e he F a b (fun _ => false) (fun _ _ _ _ => 0)]
    apply J8SourceMoment.completedScale_pos
    · exact publicSiblings_pos d e he a F _ _ (by omega) localSat
    · exact hneg
    · exact hneg
    · exact J8SourceMoment.old_nonnegative _ _ _
    · exact J8SourceMoment.old_has_assignment _ _ _ (localSat _)
    · exact J8SourceMoment.old_nonnegative _ _ _
    · exact J8SourceMoment.old_has_assignment _ _ _ (localSat _)
    · exact groupedTargets_nonempty d a off
    · have : 0 < (L:ℚ) := by exact_mod_cast (show 0<L by omega)
      positivity
    · exact physicalDenominator_pos d a he hL
  have hnum : (physicalFractions d e he F a b sign).scale.num≠0 := by
    intro hn
    have eq := (physicalFractions_exact d e he hL F a b sign).2.1
    unfold Fraction.value at eq
    rw [hn,Int.cast_zero,zero_div] at eq
    exact hscale.ne' eq.symm
  exact ⟨hd,hnum,hsZ⟩

def recoverTileRun (e : EndpointSeating d) (he : Even L) (F : OldTables d) (a : S) (sign : S→Bool)
    (i : Fin (Fintype.card (PinTile d a))) : RecoveryRun :=
  recoverRun (coordinateInt d a) (fun b => physicalFractions d e he F a b sign) i

theorem recoverTileRun_exact (e : EndpointSeating d) (he : Even L) (hL : 2<L) (F : OldTables d)
    (a : S) (sign : S→Bool) (off : d.rowLabel (pinWire d a).1≠d.pinLabel a)
    (sat : ∀ g v, ∃ z, satisfied (F g v) z=true) (i : Fin (Fintype.card (PinTile d a))) :
    (recoverTileRun d e he F a sign i).answer =
      J9R18Compiled.stencilReadTile d e he F a (fun b =>
        J9R18Compiled.firstCoefficient d e he F a b sign) i := by
  unfold recoverTileRun
  rw [recoverRun_exact _ _ _ (coordinateInt_injective d a) (fun b =>
    physicalFractions_good d e he hL F a b sign off sat)]
  have h₀ := funext (fun j => coordinateInt_exact d a j)
  have h₁ := funext (fun j => (physicalFractions_exact d e he hL F a j sign).1)
  have h₂ := funext (fun j => (physicalFractions_exact d e he hL F a j sign).2.1)
  have h₃ := funext (fun j => (physicalFractions_exact d e he hL F a j sign).2.2)
  rw [h₀,h₁,h₂,h₃]
  rfl

theorem recover_all_pins_integer (e : EndpointSeating d) (he : Even L) (hL : 2<L)
    (F : OldTables d) (sign : S→Bool)
    (off : ∀ a, d.rowLabel (pinWire d a).1≠d.pinLabel a)
    (sat : ∀ g v, ∃ z, satisfied (F g v) z=true) :
    (fun s => let w := (J9R17AllPins.orderPin d).symm s
      (recoverTileRun d e he F (J9R17AllPins.anchor d w.1) sign w.2).answer)=sign := by
  calc
    _ = J9R18Compiled.stencilReadAll d e he F
        (fun w => J9R18Compiled.firstCoefficient d e he F (J9R17AllPins.anchor d w.1) w.2 sign) := by
      funext s
      exact recoverTileRun_exact d e he hL F _ sign (off _) sat _
    _ = sign := J9R18Compiled.stencil_compiled_recovers_all d e he hL F sign off sat

#print axioms stored_normal
#print axioms recoverRun_work
#print axioms recoverRun_exact
#print axioms physicalFractions_good
#print axioms recoverTileRun_exact
#print axioms recover_all_pins_integer

end
end J9R19CompiledBits
