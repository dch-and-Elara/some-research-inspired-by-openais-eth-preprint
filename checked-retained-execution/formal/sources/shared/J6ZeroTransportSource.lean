import J6ZeroTransport
import J6NativeHeightKernel
import J6NativeHeightLift

/-! The exact receiving value of the literal J6 Cauchy zero-mode at a
zero probe. This is independent of recursive evaluation schedules. -/
namespace J6ZeroTransport

open scoped BigOperators Classical
open DenominatorBudget J6Mesh J6PhysicalPacking J6NativeHeightPort
open J6NativeHeightMesh J6NativeHeightClearing J6NativeHeightResidue
open J6NativeHeightDyadic

section Transport

variable {P R S : Type*} [Fintype P] [CommRing R] [CommRing S]

def literalRow (W : P→P→R) (p : P) (x : P→Bool) : R :=
  ∑ q, W p q * (if x q then 1 else 0)

def literalFactor (y : Bool) (z : R) : R := if y then z else 1-z

/-- Full physical finite Boolean sum before discarding unmatched rows. -/
noncomputable def literalContraction [DecidableEq P] (W : P→P→R) (A B : (P→Bool)→Bool) : R :=
  ∑ y : P→Bool, ∑ x : P→Bool,
    if A y && B x then ∏ p, literalFactor (y p) (literalRow W p x) else 0

theorem map_literalRow (f : R→+*S) (W : P→P→R) (p : P) (x : P→Bool) :
    f (literalRow W p x) = literalRow (fun p q => f (W p q)) p x := by
  rw [literalRow,literalRow,map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  cases x q <;> simp

theorem map_literalContraction [DecidableEq P] (f : R→+*S) (W : P→P→R) (A B : (P→Bool)→Bool) :
    f (literalContraction W A B) = literalContraction (fun p q => f (W p q)) A B := by
  simp only [literalContraction,map_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  split
  · rw [map_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    cases y p <;> simp [literalFactor,map_literalRow]
  · exact map_zero _

/-- Kernel center with at most one real successor: not all P×P entries
survive. This holds also in the receiving ring, not just over Q. -/
theorem row_of_partial [DecidableEq P] (read : P→Option P) (c : R)
    (p : P) (x : P→Bool) :
    literalRow (fun p q => if read p=some q then c else 0) p x =
      if ((read p).map x).getD false then c else 0 := by
  unfold literalRow
  cases hr : read p with
  | none => simp [hr]
  | some q =>
    simp only [hr,Option.map_some,Option.getD_some]
    rw [Finset.sum_eq_single_of_mem q (Finset.mem_univ _)]
    · by_cases hx : x q = true <;> simp [hx]
    · intro q' _ hq
      rw [if_neg (fun e => hq (Option.some.inj e).symm),zero_mul]

theorem contraction_of_partial [DecidableEq P] (read : P→Option P) (c : R)
    (A B : (P→Bool)→Bool) :
    literalContraction (fun p q => if read p=some q then c else 0) A B =
      residueSlot A B (fun p x => ((read p).map x).getD false) c := by
  unfold literalContraction residueSlot
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
  split
  · refine Finset.prod_congr rfl fun p _ => ?_
    rw [row_of_partial]
    cases y p <;> simp [literalFactor,ringEntry]
  · rfl

end Transport

section ActualJ6

variable {C : Type*} [DecidableEq C]

/-- A local-ring lift of the literal rational kernel, justified entrywise
by R6 at the true printed grid point. Equal rationals do not require a
homomorphism from Q to the finite ring. -/
noncomputable def localWeight (rho : C) (m l : ℕ) (h : m≤K m)
    (i : Fin (m+1)) (p q : Wire rho m (K m) l) : TwoLocal :=
  ⟨J6NativeHeightKernel.sourceWeight rho m l h i p q, by
    rw [J6NativeHeightKernel.sourceWeight_eq]
    split
    · exact actual_point_mem m i
    · exact twoLocalSubalgebra.zero_mem⟩

theorem localWeight_partial (rho : C) (m l : ℕ) (h : m≤K m)
    (i : Fin (m+1)) (p q : Wire rho m (K m) l) :
    localWeight rho m l h i p q =
      if shiftedWire rho m (K m) l h (index m i) p=some q then scalar m i else 0 := by
  apply twoLocalRat_injective
  rw [show twoLocalRat (localWeight rho m l h i p q) =
    J6NativeHeightKernel.sourceWeight rho m l h i p q from rfl,
    J6NativeHeightKernel.sourceWeight_eq]
  split <;> rfl

variable [Fintype C]

noncomputable def localContraction (rho : C) (m l : ℕ) (h : m≤K m)
    (i : Fin (m+1)) (A B : (Wire rho m (K m) l→Bool)→Bool) : TwoLocal :=
  literalContraction (localWeight rho m l h i) A B

theorem localContraction_rational (rho : C) (m l : ℕ) (h : m≤K m)
    (i : Fin (m+1)) (A B : (Wire rho m (K m) l→Bool)→Bool) :
    twoLocalRat (localContraction rho m l h i A B) =
      J6NativeHeightKernel.sourceContraction rho m l h i A B := by
  rw [localContraction,map_literalContraction]
  rfl

/-- Pushforward of the actual finite local coefficient sums. The receiving
zeroth mode is precisely the literal partial-wiring contraction. -/
theorem localContraction_receives {S : Type*} [CommRing S]
    (f : TwoLocal→+*S) (rho : C) (m l : ℕ) (h : m≤K m)
    (i : Fin (m+1)) (A B : (Wire rho m (K m) l→Bool)→Bool) :
    f (localContraction rho m l h i A B) =
      residueSlot A B (packedRead rho m (K m) l h (index m i)) (f (scalar m i)) := by
  rw [localContraction,map_literalContraction]
  have hW : (fun p q => f (localWeight rho m l h i p q)) =
      (fun p q => if shiftedWire rho m (K m) l h (index m i) p=some q then f (scalar m i) else 0) := by
    funext p q
    rw [localWeight_partial]
    split <;> simp
  rw [hW]
  exact contraction_of_partial (shiftedWire rho m (K m) l h (index m i)) (f (scalar m i)) A B

/-- The printed base scalar, composed with the native extension and ell=1
projection, gives exactly the base residue. -/
theorem native_contraction_constant (p : ℕ) (poly : Polynomial ℤ)
    (rho : C) (m l : ℕ) (h : m≤K m) (i : Fin (m+1))
    (A B : (Wire rho m (K m) l→Bool)→Bool) :
    reduceNative p poly (localContraction rho m l h i A B) =
      AdjoinRoot.of (NativeProbeRing.liftPoly p poly)
        (residueSlot A B (packedRead rho m (K m) l h (index m i))
           (reduceBase p (scalar m i))) := by
  change AdjoinRoot.of (NativeProbeRing.liftPoly p poly)
    (reduceBase p (localContraction rho m l h i A B)) = _
  rw [localContraction_receives]

/-- Actual literal zero mode followed by exact centered lifting. The raw
mesh denominator is only multiplied in the residue ring, never inverted. -/
theorem centered_literal (m base : ℕ) (rho : C) (l : ℕ) (h : m≤K m)
    (hW : Fintype.card (Wire rho m (K m) l)=M m) (i : Fin (m+1))
    (A B : (Wire rho m (K m) l→Bool)→Bool) :
    let p := J6SourcePrecision.printed m base
    let native := reduceBase p (localContraction rho m l h i A B)
    ((((sampleDen m i : ZMod (2^p))^M m*native).valMinAbs:ℚ) /
      (sampleDen m i:ℚ)^M m) = J6NativeHeightKernel.sourceContraction rho m l h i A B := by
  dsimp
  rw [J6NativeHeightKernel.full_contraction_reduction]
  exact J6NativeHeightLift.exact_centered_readout m base i hW A B _
    (reduceBase (J6SourcePrecision.printed m base)) _ (localContraction_receives _ _ _ _ _ _ _ _)

theorem one_packing_exact_receiving (m base : ℕ) (rho : C) (hC : Fintype.card C=D m) :
    ∃ l : ℕ, ∃ h : m≤K m, 2*l=L m ∧
      ∀ (A B : (Wire rho m (K m) l→Bool)→Bool) (i : Fin (m+1)),
        let p := J6SourcePrecision.printed m base
        let native := reduceBase p (localContraction rho m l h i A B)
        ((((sampleDen m i : ZMod (2^p))^M m*native).valMinAbs:ℚ) /
          (sampleDen m i:ℚ)^M m) = J6NativeHeightKernel.sourceContraction rho m l h i A B := by
  obtain ⟨l,h,hl,_,hh,_,_⟩ := J6PackingAssembly.literal_assembly m 0 (Nat.zero_le _) rho hC
  exact ⟨l,h,hl,fun A B i => centered_literal m base rho l h hh i A B⟩

end ActualJ6

#print axioms map_literalRow
#print axioms map_literalContraction
#print axioms row_of_partial
#print axioms contraction_of_partial
#print axioms localWeight_partial
#print axioms localContraction_rational
#print axioms localContraction_receives
#print axioms native_contraction_constant
#print axioms centered_literal
#print axioms one_packing_exact_receiving

end J6ZeroTransport