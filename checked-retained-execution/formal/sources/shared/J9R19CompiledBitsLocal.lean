
import J9R19CompiledBitsPrefixes
import J9R18CompiledTables

/-! Integer implementation and width of actual bounded-degree old CNF
table weights. The guard concerns physical port degree, not truth-oracle
cost. The same definition handles the real J8 selected derivative. -/
namespace J9R19CompiledBits
open scoped Classical BigOperators
open J8Physical J8EndToEnd J8J9Grouped LiteralPortCompiler
noncomputable section
set_option linter.unusedSectionVars false

theorem fprod_fits {I : Type*} (s : Finset I) (f : I→ℤ) {b : ℕ}
    (h : ∀ i∈s, Fits b (f i)) :
    Fits (b*s.card) (∏ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty => simp [Fits]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.card_insert_of_notMem ha,Nat.mul_succ]
    simpa only [Nat.add_comm] using
      (h a (Finset.mem_insert_self _ _)).mul (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem fsum_fits {I : Type*} (s : Finset I) (f : I→ℤ) {b : ℕ}
    (h : ∀ i∈s, Fits b (f i)) :
    Fits (b+s.card) (∑ i∈s,f i) := by
  induction s using Finset.induction_on with
  | empty => simp [Fits]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha,Finset.card_insert_of_notMem ha]
    have h₁ := (h a (Finset.mem_insert_self _ _)).mono (show b≤b+s.card by omega)
    have h₂ := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa only [Nat.add_assoc] using h₁.add h₂

theorem Fits.pow {w : ℕ} {a : ℤ} (h : Fits w a) (b : ℕ) :
    Fits (w*b) (a^b) := by
  induction b with
  | zero => simpa using Fits.one 0
  | succ b ih =>
    rw [pow_succ,Nat.mul_succ]
    exact ih.mul h

def bitZ (b : Bool) : ℤ := if b then 1 else 0

theorem bitZ_fits (b : Bool) : Fits 0 (bitZ b) := by
  cases b
  · simpa [bitZ] using Fits.zero 0
  · simpa [bitZ] using Fits.one 0

theorem bitZ_cast (b : Bool) : (bitZ b : ℚ) = NativeChildRealization.bitValue ℚ b := by
  cases b <;> simp [bitZ,NativeChildRealization.bitValue]

theorem kernel_fits (L : ℕ) (hL : 1≤L) : Fits (2*L) (J9FactorBounds.kernel L) := by
  have h : ((J9FactorBounds.kernel L).natAbs : ℤ) ≤ (2:ℤ)^(2*L) := by
    rw [Int.natCast_natAbs]
    have hk := J9FactorBounds.kernel_budget L hL
    omega
  unfold Fits
  exact_mod_cast h

/-- One physical row can visit at most one bit of its original column.
If the marked leg is the hit leg, the weight is the fixed -1. -/
def unaryZ (marked : Option Bool) (side : Bool) (a : ℤ) : ℤ :=
  match marked with
  | none => 1-a
  | some t => if t=side then -1 else -1+(a+a)

theorem unaryZ_cast {R : Type*} [Fintype R] [DecidableEq R] (mark : Option (R × Bool)) (r : R)
    (side : Bool) (a : ℤ) :
    (unaryZ (J8SourceMoment.marker mark r) side a : ℚ) =
      J8SourceMoment.localRow mark r side a := by
  rw [J8SourceMoment.localRow_formula]
  cases h : J8SourceMoment.marker mark r with
  | none => simp [unaryZ]
  | some t =>
    by_cases e : t=side
    · simp [unaryZ,e]
    · simp [unaryZ,e]
      ring

theorem unaryZ_fits (marked : Option Bool) (side : Bool) {b : ℕ} (a : ℤ) (ha : Fits b a) :
    Fits (b+2) (unaryZ marked side a) := by
  cases marked with
  | none =>
    exact ((Fits.one b).sub ha).mono (by omega)
  | some t =>
    by_cases same : t=side
    · simpa [unaryZ,same] using (Fits.one (b+2)).neg
    · simpa [unaryZ,same,Nat.add_assoc] using ((Fits.one (b+1)).neg).add (ha.add ha)

variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

def actualIntWeight (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (g : G) (mark : Option (LocalRow d g × Bool)) (v : LocalColumn d g)
    (z : LocalPort d v→Bool) : ℤ :=
  let w := groupWiring d e he g
  bitZ (J9R18Compiled.countedCNF z (F g v)).1 *
    ∏ r : {r : LocalRow d g // w.dest r=some v},
      unaryZ (J8SourceMoment.marker mark r.val) (w.leg r.val)
        (J9FactorBounds.kernel L * bitZ (z (w.port r.val v r.prop)))

theorem actualIntWeight_exact (e : EndpointSeating d) (he : Even L) (hL : 1≤L)
    (F : OldTables d) (g : G) (mark : Option (LocalRow d g × Bool)) (v : LocalColumn d g)
    (z : LocalPort d v→Bool) :
    (actualIntWeight d e he F g mark v z : ℚ) = J9R18Compiled.localWeight d e he F g mark v z := by
  rw [← J9R18Compiled.literalScanWeight_exact]
  unfold actualIntWeight J9R18Compiled.literalScanWeight
  dsimp only
  push_cast
  have hbits (b : Bool) : (bitZ b : ℚ) = indicator ℚ b := by cases b <;> simp [bitZ,indicator]
  rw [hbits]
  congr 1
  apply Finset.prod_congr rfl
  intro r _
  rw [unaryZ_cast,Int.cast_mul,bitZ_cast,printed_amplitude_integral L hL he]

theorem actualIntWeight_fits (e : EndpointSeating d) (he : Even L) (hL : 1≤L)
    (F : OldTables d) (g : G) (mark : Option (LocalRow d g × Bool)) (v : LocalColumn d g)
    (z : LocalPort d v→Bool) :
    Fits (2*L+2) (actualIntWeight d e he F g mark v z) := by
  let w := groupWiring d e he g
  let Q := {r : LocalRow d g // w.dest r=some v}
  let entry (r : Q) := unaryZ (J8SourceMoment.marker mark r.val) (w.leg r.val)
    (J9FactorBounds.kernel L * bitZ (z (w.port r.val v r.prop)))
  have hEntry (r : Q) : Fits (2*L+2) (entry r) := by
    apply unaryZ_fits
    simpa only [Nat.add_zero] using (kernel_fits L hL).mul (bitZ_fits (z (w.port r.val v r.prop)))
  have hc : (Finset.univ : Finset Q).card≤1 := by
    rw [Finset.card_univ]
    exact J9R18Compiled.shiftedRows_per_original_column d e he g v
  have hp := (fprod_fits Finset.univ entry (fun i _ => hEntry i)).mono
    (((Nat.mul_le_mul_left (2*L+2)) hc).trans_eq (Nat.mul_one _))
  change Fits (2*L+2) (bitZ (J9R18Compiled.countedCNF z (F g v)).1 * ∏ r : Q, entry r)
  simpa only [Nat.zero_add] using (bitZ_fits (J9R18Compiled.countedCNF z (F g v)).1).mul hp

def actualIntMass (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (g : G) (mark : Option (LocalRow d g × Bool)) (v : LocalColumn d g) : ℤ :=
  ∑ z : LocalPort d v→Bool,actualIntWeight d e he F g mark v z

theorem actualIntMass_exact (e : EndpointSeating d) (he : Even L) (hL : 1≤L) (F : OldTables d)
    (g : G) (mark : Option (LocalRow d g × Bool)) (v : LocalColumn d g) :
    (actualIntMass d e he F g mark v : ℚ)=J9R18Compiled.massAt d e he F g mark v := by
  unfold actualIntMass J9R18Compiled.massAt
  simp only [Int.cast_sum,actualIntWeight_exact d e he hL]

theorem actualIntMass_fits (e : EndpointSeating d) (he : Even L) (hL : 1≤L) (F : OldTables d)
    (g : G) (mark : Option (LocalRow d g × Bool)) (v : LocalColumn d g)
    (arity : Fintype.card (P v.val)≤3) :
    Fits (2*L+10) (actualIntMass d e he F g mark v) := by
  have h := fsum_fits (Finset.univ : Finset (LocalPort d v→Bool))
    (actualIntWeight d e he F g mark v) (fun z _ => actualIntWeight_fits d e he hL F g mark v z)
  have hc : (Finset.univ : Finset (LocalPort d v→Bool)).card ≤ 8 := by
    simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool]
    exact Nat.pow_le_pow_right (by decide) arity
  exact h.mono (by omega)

#print axioms fprod_fits
#print axioms fsum_fits
#print axioms kernel_fits
#print axioms unaryZ_cast
#print axioms unaryZ_fits
#print axioms actualIntWeight_exact
#print axioms actualIntWeight_fits
#print axioms actualIntMass_exact
#print axioms actualIntMass_fits
end
end J9R19CompiledBits
