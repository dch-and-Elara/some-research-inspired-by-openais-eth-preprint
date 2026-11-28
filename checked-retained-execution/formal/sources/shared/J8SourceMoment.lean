import LiteralPortCompiler
import NativeCompletedRecovery
import NativeChildRealization

/-!
J8 finite source/target identification, from the old subdivision and unary
pin truth tables to the rational completed first coefficient. The supplied
geometry describes which (at most one) old nonpin column port hits each
subdivision at zero, and which actual row-port allocations target the tile.
Higher coefficients of baseline wires are arbitrary. No interpolation,
probe-ring, or source packing construction is repeated here.
-/

namespace J8SourceMoment

open scoped BigOperators Polynomial Classical
open Polynomial
open LiteralPortCompiler (affine truth truth_equality truth_pin)

noncomputable section

section Local

variable {K : Type*} [CommRing K]

def twoBits (a b : Bool) : Bool → Bool
  | false => a
  | true => b

def oldEquality (x y : K) : K :=
  ∑ a : Bool, ∑ b : Bool,
    truth (LiteralPortCompiler.equality false true) (twoBits a b) * (affine a x * affine b y)

/-- Exactly one actual port conventionally selects the mode. The other
port keeps its baseline factor. Both are weighted by the same old table. -/
def selectedEquality (right : Bool) (x y : K) : K :=
  ∑ a : Bool, ∑ b : Bool,
    truth (LiteralPortCompiler.equality false true) (twoBits a b) *
      (if right then affine a x * LiteralPortCompiler.slope b else LiteralPortCompiler.slope a * affine b y)

theorem oldEquality_eq (x y : K) : oldEquality x y = TargetDerivative.equality x y := by
  simp [oldEquality, truth_equality, twoBits, affine, TargetDerivative.equality]
  ac_rfl

theorem selectedEquality_eq (right : Bool) (x y : K) :
    selectedEquality right x y = -1 + 2 * (if right then x else y) := by
  cases right <;>
    simp [selectedEquality, truth_equality, twoBits, affine, LiteralPortCompiler.slope] <;> ring

/-- No variation of the selected leg's baseline enters its marked factor. -/
theorem one_port_update (right : Bool) (x y k : K) :
    oldEquality (x + if right then 0 else k) (y + if right then k else 0) =
      oldEquality x y + k * selectedEquality right x y := by
  cases right <;> simp [oldEquality_eq, selectedEquality_eq, TargetDerivative.equality] <;> ring

def rowFactor (selected : Option Bool) (x y : K) : K :=
  selected.elim (oldEquality x y) (fun right => selectedEquality right x y)

theorem map_rowFactor {L : Type*} [CommRing L] (f : K →+* L)
    (selected : Option Bool) (x y : K) :
    f (rowFactor selected x y) = rowFactor selected (f x) (f y) := by
  cases selected with
  | none => simp [rowFactor, oldEquality_eq, TargetDerivative.equality]
  | some right =>
    have h2 : f (2 : K) = (2 : L) := by simpa only [Nat.cast_ofNat] using (map_natCast f 2)
    cases right <;> simp [rowFactor, selectedEquality_eq, h2]

end Local

structure Child (R Ω : Type*) where
  c : ℚ
  /-- Which leg is hit, and the bit at the matched nonpin column port. -/
  hit : R → Option (Bool × (Ω → Bool))
  /-- Product of the unchanged nonpin old column tables. -/
  oldWeight : Ω → ℚ

variable {R Ω S : Type*}

/-- Layout assumption encoded by the type: every baseline hit reads a
nonpin column bit (in Ω), never a unary pin variable (indexed by S). -/
def input0 (d : Child R Ω) (x : Ω) (r : R) (right : Bool) : ℚ :=
  match d.hit r with
  | none => 0
  | some (side, bit) =>
    if side = right then d.c * NativeChildRealization.bitValue ℚ (bit x) else 0

def marker [DecidableEq R] (marked : Option (R × Bool)) (r : R) : Option Bool :=
  marked.bind fun p => if p.1 = r then some p.2 else none

def baseArgument (d : Child R Ω)
    (higher : ((S → Bool) × Ω) → R → Bool → ℚ[X])
    (x : (S → Bool) × Ω) (r : R) (right : Bool) : ℚ[X] :=
  C (input0 d x.2 r right) + X * higher x r right

def pinWeight [Fintype S] (sign bits : S → Bool) : ℚ :=
  ∏ i : S, truth (LiteralPortCompiler.pin i (sign i)) bits

theorem pinWeight_iff [Fintype S] (sign bits : S → Bool) :
    pinWeight sign bits = if bits = sign then 1 else 0 := by
  classical
  by_cases h : bits = sign
  · subst bits
    simp [pinWeight, truth_pin]
  · rw [if_neg h, pinWeight]
    obtain ⟨v,hv⟩ := not_forall.mp (show ¬∀ i, bits i = sign i from fun H => h (funext H))
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [truth_pin,hv])

variable [Fintype R] [DecidableEq R] [Fintype Ω] [Fintype S] [DecidableEq S]

def weighted (d : Child R Ω) (marked : Option (R × Bool)) (x : Ω) : ℚ :=
  d.oldWeight x *
    ∏ r : R, rowFactor (marker marked r) (input0 d x r false) (input0 d x r true)

/-- Finite original child sum, retaining the old assignments, literal pin
indicators and two-leg truth tables. Incoming target and outgoing source
are selected by the marker and the explicit per-assignment feature. -/
def genuineChild (d : Child R Ω) (sign : S → Bool)
    (higher : ((S → Bool) × Ω) → R → Bool → ℚ[X])
    (marked : Option (R × Bool)) (feature : ((S → Bool) × Ω) → ℚ) : ℚ[X] :=
  ∑ x : Ω, ∑ bits : S → Bool,
    C (pinWeight sign bits * (d.oldWeight x * feature (bits,x))) *
      ∏ r : R, rowFactor (marker marked r)
        (baseArgument d higher (bits,x) r false) (baseArgument d higher (bits,x) r true)

theorem childConstant (d : Child R Ω) (sign : S → Bool)
    (higher : ((S → Bool) × Ω) → R → Bool → ℚ[X])
    (marked : Option (R × Bool)) (feature : ((S → Bool) × Ω) → ℚ) :
    (genuineChild d sign higher marked feature).coeff 0 =
      ∑ x : Ω, weighted d marked x * feature (sign,x) := by
  classical
  let ev : ℚ[X] →+* ℚ := Polynomial.evalRingHom 0
  rw [Polynomial.coeff_zero_eq_eval_zero]
  change ev (genuineChild d sign higher marked feature) = _
  have hb (x : (S → Bool) × Ω) (r : R) (right : Bool) :
      ev (baseArgument d higher x r right) = input0 d x.2 r right := by
    simp [ev, baseArgument]
  have hC (v : ℚ) : ev (C v) = v := by simp [ev]
  simp only [genuineChild, map_sum, map_mul, map_prod, map_rowFactor, hb, hC, pinWeight_iff]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, one_mul, zero_mul, Fintype.sum_ite_eq']
  unfold weighted
  ring

omit [Fintype R] [DecidableEq R] [Fintype Ω] [Fintype S] [DecidableEq S] in
/-- Independently of all higher local coefficients, each baseline
argument reads zero or a nonpositive multiple of a Boolean bit. -/
theorem input0_nonpos (d : Child R Ω) (negative : d.c < 0)
    (x : Ω) (r : R) (right : Bool) : input0 d x r right ≤ 0 := by
  unfold input0
  cases d.hit r with
  | none => simp
  | some p =>
    rcases p with ⟨b,rd⟩
    by_cases h : b = right
    · cases hb : rd x <;> simp [h, hb, NativeChildRealization.bitValue, negative.le]
    · simp [h]

def baselineMass (d : Child R Ω) : ℚ := ∑ x : Ω, weighted d none x

def markedMass (d : Child R Ω) (port : R × Bool) : ℚ :=
  ∑ x : Ω, weighted d (some port) x

theorem baselineMass_pos (d : Child R Ω) (negative : d.c < 0)
    (nonneg : ∀ x, 0 ≤ d.oldWeight x) (valid : ∃ x, 0 < d.oldWeight x) :
    0 < baselineMass d := by
  unfold baselineMass
  simpa only [weighted, marker, Option.bind_none, rowFactor, Option.elim_none, oldEquality_eq] using
    TargetDerivative.baseline_sum_positive d.oldWeight
      (fun x r => input0 d x r false) (fun x r => input0 d x r true) nonneg valid
      (fun x r => input0_nonpos d negative x r false)
      (fun x r => input0_nonpos d negative x r true)

omit [Fintype Ω] in
theorem marked_explicit (d : Child R Ω) (p : R × Bool) (x : Ω) :
    weighted d (some p) x =
      d.oldWeight x * (-1 + 2 * input0 d x p.1 (!p.2)) *
        ∏ r ∈ Finset.univ.erase p.1,
          TargetDerivative.equality (input0 d x r false) (input0 d x r true) := by
  classical
  have hs : ∀ r ∈ Finset.univ.erase p.1,
      rowFactor (marker (some p) r) (input0 d x r false) (input0 d x r true) =
        TargetDerivative.equality (input0 d x r false) (input0 d x r true) := by
    intro r hr
    have hn := (Finset.mem_erase.mp hr).1
    simp [marker, Ne.symm hn, rowFactor, oldEquality_eq]
  unfold weighted
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ p.1), Finset.prod_congr rfl hs]
  rw [← mul_assoc]
  congr 2
  cases h : p.2 <;> simp [marker, rowFactor, selectedEquality_eq, h]

theorem markedMass_neg (d : Child R Ω) (p : R × Bool) (negative : d.c < 0)
    (nonneg : ∀ x, 0 ≤ d.oldWeight x) (valid : ∃ x, 0 < d.oldWeight x) :
    markedMass d p < 0 := by
  have hg (x : Ω) :
      0 < ∏ r ∈ Finset.univ.erase p.1,
         TargetDerivative.equality (input0 d x r false) (input0 d x r true) :=
    Finset.prod_pos fun r _ => TargetDerivative.baseline_equality_positive _ _
      (input0_nonpos d negative x r false) (input0_nonpos d negative x r true)
  have hrow (x : Ω) : -1 + 2 * input0 d x p.1 (!p.2) < 0 :=
    TargetDerivative.target_derivative_negative _ (input0_nonpos d negative x p.1 (!p.2))
  unfold markedMass
  apply neg_pos.mp
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_pos'
  · intro x hx
    rw [marked_explicit]
    exact neg_nonneg.mpr (mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (nonneg x) (hrow x).le) (hg x).le)
  · obtain ⟨x,hx⟩ := valid
    refine ⟨x, Finset.mem_univ _, ?_⟩
    rw [marked_explicit]
    exact neg_pos.mpr (mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hx (hrow x)) (hg x))

section Source

variable {n : ℕ}

/-- The actual mode feature on a tile; `other` is the sum over its real
nonpin columns. The selected pins enter as their ordinary Boolean port bits. -/
def sourceFeature (pins : Fin n → S) (coord : Fin n → ℚ)
    (other : Fin n → Ω → ℚ) (b : Fin n) (x : (S → Bool) × Ω) : ℚ :=
  other b x.2 + ∑ i : Fin n,
    NativeMomentReconstruction.bitValue (x.1 (pins i)) * coord i ^ (b : ℕ)

def nonpinBackground (d : Child R Ω) (other : Fin n → Ω → ℚ) (b : Fin n) : ℚ :=
  (∑ x : Ω, weighted d none x * other b x) / baselineMass d

theorem sourceConstant_exact (d : Child R Ω) (sign : S → Bool)
    (higher : ((S → Bool) × Ω) → R → Bool → ℚ[X])
    (pins : Fin n → S) (coord : Fin n → ℚ) (other : Fin n → Ω → ℚ) (b : Fin n)
    (mass_ne : baselineMass d ≠ 0) :
    (genuineChild d sign higher none (sourceFeature pins coord other b)).coeff 0 =
    baselineMass d * (nonpinBackground d other b +
      NativeMomentReconstruction.moments coord (fun i => NativeMomentReconstruction.bitValue (sign (pins i))) b) := by
  rw [childConstant]
  simp only [sourceFeature, mul_add, Finset.sum_add_distrib,
    NativeMomentReconstruction.moments, ← Finset.sum_mul]
  rw [nonpinBackground, mul_div_cancel₀ _ mass_ne]
  rfl

end Source

/-- Actual outer target slope at coordinate i=0. No assumption on higher
terms is needed. The `tail` holds the subsequent (already normalized) terms. -/
def exactSlope (c α denom : ℚ) (b : ℕ) : ℚ := c * α * 2^b / denom^(b+1)

def outerKernel (c α denom : ℚ) (b : ℕ) (tail : ℚ[X]) : ℚ[X] :=
  X * (C (exactSlope c α denom b) + X * tail)

theorem outerKernel_zero (c α denom : ℚ) (b : ℕ) (tail : ℚ[X]) :
    (outerKernel c α denom b tail).coeff 0 = 0 := by
  simp [outerKernel, Polynomial.mul_coeff_zero]

theorem outerKernel_first (c α denom : ℚ) (b : ℕ) (tail : ℚ[X]) :
    (outerKernel c α denom b tail).coeff 1 = exactSlope c α denom b := by
  simp [outerKernel, Polynomial.mul_coeff_one, Polynomial.mul_coeff_zero]

section Assembly

variable {RS OS SS RT OT ST : Type*}
variable [Fintype RS] [DecidableEq RS] [Fintype OS] [Fintype SS] [DecidableEq SS]
variable [Fintype RT] [DecidableEq RT] [Fintype OT] [Fintype ST] [DecidableEq ST]
variable {n : ℕ}

/-- Original source child times actual targeted allocation sum, with the
public factor representing the product of the other zero-mode siblings. -/
def completedTile (pub : ℚ[X]) (src : Child RS OS) (tgt : Child RT OT)
    (srcSigns : SS → Bool) (tgtSigns : ST → Bool)
    (sh : ((SS → Bool) × OS) → RS → Bool → ℚ[X])
    (th : ((ST → Bool) × OT) → RT → Bool → ℚ[X])
    (pins : Fin n → SS) (coord : Fin n → ℚ) (other : Fin n → OS → ℚ)
    (s : Finset (RT × Bool)) (α : ℚ) (denom : RT × Bool → ℚ)
    (rest : RT × Bool → ℚ[X]) (b : Fin n) : ℚ[X] :=
  NativeCompletedRecovery.completed s pub
    (genuineChild src srcSigns sh none (sourceFeature pins coord other b))
    (fun p => outerKernel tgt.c α (denom p) b (rest p))
    (fun p => genuineChild tgt tgtSigns th (some p) (fun _ => 1))

/-- The displayed J8 multiplier, from the actual marked-port sums and the
unchanged nonpin zero-mode mass. No pin value appears in this definition. -/
def completedScale (pub : ℚ[X]) (src : Child RS OS) (tgt : Child RT OT)
    (s : Finset (RT × Bool)) (α : ℚ) (denom : RT × Bool → ℚ) (b : ℕ) : ℚ :=
  (pub.coeff 0 * ∑ p ∈ s, exactSlope tgt.c α (denom p) b * markedMass tgt p) *
    baselineMass src

omit [Fintype SS] [DecidableEq SS] [Fintype ST] [DecidableEq ST] in
theorem completedScale_pos (pub : ℚ[X]) (src : Child RS OS) (tgt : Child RT OT)
    (s : Finset (RT × Bool)) (α : ℚ) (denom : RT × Bool → ℚ) (b : ℕ)
    (pub_pos : 0 < pub.coeff 0) (src_neg : src.c < 0) (tgt_neg : tgt.c < 0)
    (src_nonneg : ∀ x, 0 ≤ src.oldWeight x) (src_valid : ∃ x, 0 < src.oldWeight x)
    (tgt_nonneg : ∀ x, 0 ≤ tgt.oldWeight x) (tgt_valid : ∃ x, 0 < tgt.oldWeight x)
    (nonempty : s.Nonempty) (alpha_pos : 0 < α) (denom_pos : ∀ p ∈ s, 0 < denom p) :
    0 < completedScale pub src tgt s α denom b := by
  unfold completedScale
  apply mul_pos _ (baselineMass_pos src src_neg src_nonneg src_valid)
  apply TargetDerivative.completed_scale_positive s nonempty _ _ _ pub_pos
  · intro p hp
    exact TargetDerivative.target_kernel_slope_negative tgt.c α (denom p) b tgt_neg alpha_pos
      (denom_pos p hp)
  · intro p hp
    exact markedMass_neg tgt p tgt_neg tgt_nonneg tgt_valid

/-- The source moment identity, with genuine literal tables in both
affected children and without a cancellation or a weight-factor premise. -/
theorem completed_first_exact (pub : ℚ[X]) (src : Child RS OS) (tgt : Child RT OT)
    (srcSigns : SS → Bool) (tgtSigns : ST → Bool)
    (sh : ((SS → Bool) × OS) → RS → Bool → ℚ[X])
    (th : ((ST → Bool) × OT) → RT → Bool → ℚ[X])
    (pins : Fin n → SS) (coord : Fin n → ℚ) (other : Fin n → OS → ℚ)
    (s : Finset (RT × Bool)) (α : ℚ) (denom : RT × Bool → ℚ)
    (rest : RT × Bool → ℚ[X]) (b : Fin n) (mass_ne : baselineMass src ≠ 0) :
    (completedTile pub src tgt srcSigns tgtSigns sh th pins coord other s α denom rest b).coeff 1 =
      completedScale pub src tgt s α denom b *
        (nonpinBackground src other b +
          NativeMomentReconstruction.moments coord
            (fun i => NativeMomentReconstruction.bitValue (srcSigns (pins i))) b) := by
  unfold completedTile NativeCompletedRecovery.completed
  rw [TargetDerivative.first_completed_target _ _ _ _ _ (fun p _ => outerKernel_zero _ _ _ _ _)]
  rw [sourceConstant_exact src _ _ _ _ _ _ mass_ne]
  simp only [outerKernel_first, childConstant, mul_one, markedMass, completedScale, mul_assoc]

/-- Rational postprocessor at distinct exact coordinates. This starts after
denominator clearing and centered lifting, so parity collisions among
different coordinates do not affect the inverse. -/
theorem recover_from_exact_completed
    (pub : ℚ[X]) (src : Child RS OS) (tgt : Child RT OT)
    (srcSigns : SS → Bool) (tgtSigns : ST → Bool)
    (sh : ((SS → Bool) × OS) → RS → Bool → ℚ[X])
    (th : ((ST → Bool) × OT) → RT → Bool → ℚ[X])
    (pins : Fin n → SS) (coord : Fin n → ℚ) (other : Fin n → OS → ℚ)
    (s : Fin n → Finset (RT × Bool)) (α : ℚ) (denom : Fin n → RT × Bool → ℚ)
    (rest : Fin n → RT × Bool → ℚ[X])
    (distinct : Function.Injective coord)
    (pub_pos : 0 < pub.coeff 0) (src_neg : src.c < 0) (tgt_neg : tgt.c < 0)
    (src_nonneg : ∀ x, 0 ≤ src.oldWeight x) (src_valid : ∃ x, 0 < src.oldWeight x)
    (tgt_nonneg : ∀ x, 0 ≤ tgt.oldWeight x) (tgt_valid : ∃ x, 0 < tgt.oldWeight x)
    (nonempty : ∀ b, (s b).Nonempty) (alpha_pos : 0 < α)
    (denom_pos : ∀ b p, p ∈ s b → 0 < denom b p) :
    NativeMomentReconstruction.decodeBits coord
      (fun b => completedScale pub src tgt (s b) α (denom b) b) (nonpinBackground src other)
      (fun b => (completedTile pub src tgt srcSigns tgtSigns sh th
        pins coord other (s b) α (denom b) (rest b) b).coeff 1) = srcSigns ∘ pins := by
  let sc := fun b : Fin n => completedScale pub src tgt (s b) α (denom b) b
  let obs := fun b : Fin n => (completedTile pub src tgt srcSigns tgtSigns sh th
        pins coord other (s b) α (denom b) (rest b) b).coeff 1
  have hsc (b : Fin n) : sc b ≠ 0 :=
    (completedScale_pos pub src tgt (s b) α (denom b) b pub_pos src_neg tgt_neg
      src_nonneg src_valid tgt_nonneg tgt_valid (nonempty b) alpha_pos (denom_pos b)).ne'
  have decode : NativeMomentReconstruction.decode coord sc (nonpinBackground src other) obs =
      fun i => NativeMomentReconstruction.bitValue (srcSigns (pins i)) := by
    apply NativeMomentReconstruction.decode_scaled _ _ _ _ _ distinct hsc
    intro b
    exact completed_first_exact pub src tgt srcSigns tgtSigns sh th pins coord other
      (s b) α (denom b) (rest b) b (baselineMass_pos src src_neg src_nonneg src_valid).ne'
  change NativeMomentReconstruction.decodeBits coord sc _ obs = _
  funext i
  unfold NativeMomentReconstruction.decodeBits
  rw [decode]
  cases srcSigns (pins i) <;> simp [NativeMomentReconstruction.bitValue]

end Assembly


#print axioms one_port_update
#print axioms childConstant
#print axioms baselineMass_pos
#print axioms marked_explicit
#print axioms markedMass_neg
#print axioms sourceConstant_exact
#print axioms completedScale_pos
#print axioms completed_first_exact
#print axioms recover_from_exact_completed

end
end J8SourceMoment
