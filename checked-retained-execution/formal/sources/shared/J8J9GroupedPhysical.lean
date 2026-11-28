import J8J9Grouped

/-! Integer forms of the actual packet child coefficients. -/

namespace J8J9Grouped
open scoped Polynomial BigOperators Classical
open Polynomial DyadicProbeCompiler J8EndToEnd J8Physical

noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

def table (F : OldTables d) (g : G) (x : LocalBits d g) : ℤ :=
  ∏ v : LocalColumn d g, LiteralPortCompiler.truth (F g v) (x v)

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [DecidableEq V]
  [Fintype G] [DecidableEq Packet] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem table_cast (F : OldTables d) (g : G) (x : LocalBits d g) :
    (table d F g x : Source) = physicalTableWeight d F g x := by
  change (Int.castRingHom Source) (table d F g x) = _
  simp only [table, physicalTableWeight, map_prod, LiteralPortCompiler.map_truth]

def bit (b : Bool) : ℤ := if b then 1 else 0

theorem bit_cast (b : Bool) : (bit b : Source) = sourceBit b := by
  cases b <;> simp [bit, sourceBit]

def argument (e : EndpointSeating d) (even : Even L) (g : G)
    (x : (LocalPin d g → Bool) × LocalBits d g) (r : LocalRow d g) (leg : Bool) : ℤ :=
  ((localHit d e even r).map fun p =>
    if p.1 = leg then J9FactorBounds.kernel L * bit (x.2 p.2.1 p.2.2) else 0).getD 0

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
  [Fintype G] [DecidableEq G] [DecidableEq Packet] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem argument_cast (e : EndpointSeating d) (even : Even L) (tail : IntegralArguments d)
    (g : G) (x : (LocalPin d g → Bool) × LocalBits d g) (r : LocalRow d g) (leg : Bool) :
    (argument d e even g x r leg : Source) =
      (physicalBase d e even (J9FactorBounds.kernel L) tail g x r leg).coeff 0 := by
  simp only [argument, physicalBase, Polynomial.coeff_add, Polynomial.coeff_C_zero,
    Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, add_zero]
  cases hh : localHit d e even r with
  | none => simp
  | some p =>
    by_cases h : p.1 = leg <;> simp [h, bit_cast]

def feature (a : S) (b : Fin (Fintype.card (PinTile d a)))
    (x : (LocalPin d (d.pinLabel a) → Bool) × LocalBits d (d.pinLabel a)) : ℤ :=
  (∑ q : OldTile d a,
    (ordinal d (ordinaryWire d q.1) : ℤ)^(b : ℕ) *
      bit (x.2 (tileOldInSource d q).1 (tileOldInSource d q).2)) +
  ∑ i : Fin (Fintype.card (PinTile d a)),
    bit (x.1 (tilePinInSource d (pinEnumeration d a i))) *
      (ordinal d (pinWire d (pinEnumeration d a i).1) : ℤ)^(b : ℕ)

omit [Fintype R] [DecidableEq R] [DecidableEq S] [DecidableEq V]
  [Fintype G] [DecidableEq G] [(v : V) → DecidableEq (P v)] in
theorem feature_cast (a : S) (b : Fin (Fintype.card (PinTile d a)))
    (x : (LocalPin d (d.pinLabel a) → Bool) × LocalBits d (d.pinLabel a)) :
    (feature d a b x : Source) = integralFeature d a b x := by
  simp only [feature, integralFeature, Int.cast_add, Int.cast_sum, Int.cast_mul,
    Int.cast_pow, Int.cast_natCast, bit_cast]

def child (e : EndpointSeating d) (even : Even L) (F : OldTables d) (sign : S → Bool)
    (g : G) (mark : Option (LocalRow d g × Bool))
    (feat : ((LocalPin d g → Bool) × LocalBits d g) → ℤ) : ℤ :=
  integerChild (table d F g) (fun i : LocalPin d g => sign i.1)
    (argument d e even g) mark feat

omit [Fintype G] [DecidableEq Packet] in
theorem child_cast (e : EndpointSeating d) (even : Even L) (F : OldTables d) (sign : S → Bool)
    (tail : IntegralArguments d) (g : G) (mark : Option (LocalRow d g × Bool))
    (feat : ((LocalPin d g → Bool) × LocalBits d g) → ℤ)
    (f : ((LocalPin d g → Bool) × LocalBits d g) → Source)
    (h : ∀ x, (feat x : Source) = f x) :
    (child d e even F sign g mark feat : Source) =
      (liftedGroup d F (physicalBase d e even (J9FactorBounds.kernel L) tail) sign g mark f).coeff 0 :=
  integerChild_cast _ _ _ _ _ _ _ _ (table_cast d F g) (argument_cast d e even tail g) h

def pub (e : EndpointSeating d) (even : Even L) (a : S) (F : OldTables d) (sign : S → Bool) : ℤ :=
  ∏ g ∈ ((Finset.univ : Finset G).erase (d.pinLabel a)).erase (d.rowLabel (pinWire d a).1),
    child d e even F sign g none (fun _ => 1)

omit [DecidableEq Packet] in
theorem public_cast (e : EndpointSeating d) (even : Even L) (a : S) (F : OldTables d)
    (sign : S → Bool) (tail : IntegralArguments d) :
    (pub d e even a F sign : Source) =
      (liftedPublic d a F (physicalBase d e even (J9FactorBounds.kernel L) tail) sign).coeff 0 := by
  simp only [pub, liftedPublic, Int.cast_prod, Polynomial.coeff_zero_prod]
  exact Finset.prod_congr rfl fun g hg =>
    child_cast d e even F sign tail g none _ _ (fun _ => Int.cast_one)

def physicalDen (a : S) (b : ℕ) (j : TargetPorts d a) : ℤ :=
  (integerDenominator d a j)^(b+1)

def clear (a : S) (b : ℕ) : ℤ := denominator (groupedTargets d a) (physicalDen d a b)

def exactNum (e : EndpointSeating d) (even : Even L) (a : S) (F : OldTables d)
    (sign : S → Bool) (b : Fin (Fintype.card (PinTile d a))) : ℤ :=
  numerator (groupedTargets d a) (physicalDen d a b) (J9FactorBounds.slope L b)
    (pub d e even a F sign) (child d e even F sign (d.pinLabel a) none (feature d a b))
    (fun j => child d e even F sign (d.rowLabel (pinWire d a).1) (some j) (fun _ => 1))

omit [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
  [Fintype G] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem clear_positive_odd (even : Even L) (hL : 2 < L) (a : S) (b : ℕ) :
    0 < clear d a b ∧ Odd (clear d a b) := by
  apply denominator_positive_odd
  intro j hj
  exact ⟨pow_pos (groupedTargets_denom d a even hL hj).1 _, (groupedTargets_denom d a even hL hj).2.pow⟩

set_option maxHeartbeats 500000 in
theorem exactNum_native (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
    (k : ℕ) (length : L = 2^k) (a : S) (F : OldTables d) (sign : S → Bool)
    (tail : IntegralArguments d) (b : Fin (Fintype.card (PinTile d a)))
    (kt : TargetPorts d a → Source[X]) :
    let base := physicalBase d e even (J9FactorBounds.kernel L) tail
    let s := groupedTargets d a
    let pn := liftedPublic d a F base sign
    let src := liftedGroup d F base sign (d.pinLabel a) none (integralFeature d a b)
    let tgt := fun j => liftedGroup d F base sign (d.rowLabel (pinWire d a).1) (some j) (fun _ => 1)
    let ker := physicalKernel d a even hL (J9FactorBounds.kernel L) b kt
    (exactNum d e even a F sign b : ℚ) = (clear d a b : ℚ) *
      ((2:ℚ)^(k+1+(b:ℕ)) * rationalMap ((groupedNormalized s pn src tgt ker).coeff 0)) := by
  dsimp only
  have hp := congrArg rationalMap (public_cast d e even a F sign tail)
  have hs := congrArg rationalMap (child_cast d e even F sign tail (d.pinLabel a) none
    (feature d a b) (integralFeature d a b) (feature_cast d a b))
  have ht (j : TargetPorts d a) := congrArg rationalMap
    (child_cast d e even F sign tail (d.rowLabel (pinWire d a).1) (some j)
      (fun _ => 1) (fun _ => 1) (fun _ => Int.cast_one))
  simp only [map_intCast] at hp hs ht
  have hd (i : TargetPorts d a) (hi : i ∈ groupedTargets d a) : physicalDen d a b i ≠ 0 :=
    (pow_pos (groupedTargets_denom d a even hL hi).1 _).ne'
  unfold exactNum
  rw [numerator_cast _ _ _ _ _ _ hd, hp, hs]
  congr 1
  simp only [groupedNormalized, Polynomial.mul_coeff_zero, Polynomial.finset_sum_coeff, map_mul,
    map_sum]
  rw [mul_left_comm ((2:ℚ) ^ _) _ _]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [ht j, ← mul_assoc, constructed_kernel_normalized d a even hL _ _ _ j hj]
  simp only [J9FactorBounds.slope, physicalDen, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
    Int.cast_ofNat, denominator_cast]
  have hl : (L:ℚ) = (2:ℚ)^k := by exact_mod_cast length
  rw [hl, pow_add (2:ℚ) (k+1) (b:ℕ), pow_succ (2:ℚ) k]
  ring

#print axioms child_cast
#print axioms public_cast
#print axioms clear_positive_odd
#print axioms exactNum_native

end
end J8J9Grouped
