import J8RelaxedKernel
import J8PhysicalRecovery
set_option warningAsError true
namespace J8Physical.Relaxed
open scoped Polynomial BigOperators Classical
open Polynomial
noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype V] [DecidableEq V] [DecidableEq G] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]
def localChild (e : RowEndpointSeating d) (even : Even L) (g : G) (c : ℚ)
    (F : (v : LocalColumn d g) → LiteralPortCompiler.CNF (LocalPort d v)) :
    J8SourceMoment.Child (LocalRow d g) (LocalBits d g) :=
  J8SourceMoment.literalChild (groupWiring d e even g) c F

variable [Fintype S] [DecidableEq S]

omit [DecidableEq Packet] in
/-- The public baseline and every targeted local derivative constant
depend only on physical old nonpin tables, not on the unary pin signs.
The higher probe coefficients need not enjoy this independence. -/
theorem physicalMarked_constant (e : RowEndpointSeating d) (even : Even L) (g : G) (c : ℚ)
    (F : (v : LocalColumn d g) → LiteralPortCompiler.CNF (LocalPort d v))
    (sign : LocalPin d g → Bool)
    (higher : ((LocalPin d g → Bool) × LocalBits d g) → LocalRow d g → Bool → ℚ[X])
    (marked : Option (LocalRow d g × Bool)) :
    (J8SourceMoment.genuineChild (localChild d e even g c F) sign higher marked (fun _ => 1)).coeff 0 =
      ∑ x : LocalBits d g, J8SourceMoment.weighted (localChild d e even g c F) marked x := by
  rw [J8SourceMoment.childConstant]
  simp only [mul_one]

omit [DecidableEq Packet] in
theorem physicalMarked_sign_independent (e : RowEndpointSeating d) (even : Even L) (g : G) (c : ℚ)
    (F : (v : LocalColumn d g) → LiteralPortCompiler.CNF (LocalPort d v))
    (sign sign' : LocalPin d g → Bool)
    (higher higher' : ((LocalPin d g → Bool) × LocalBits d g) → LocalRow d g → Bool → ℚ[X])
    (marked : Option (LocalRow d g × Bool)) :
    (J8SourceMoment.genuineChild (localChild d e even g c F) sign higher marked (fun _ => 1)).coeff 0 =
      (J8SourceMoment.genuineChild (localChild d e even g c F) sign' higher' marked (fun _ => 1)).coeff 0 := by
  rw [physicalMarked_constant, physicalMarked_constant]

variable [Fintype G]

def publicSiblings (e : RowEndpointSeating d) (even : Even L) (a : S)
    (F : OldTables d) (higher : RestArguments d) (sign : S → Bool) : ℚ[X] :=
  ∏ g ∈ ((Finset.univ : Finset G).erase (d.pinLabel a)).erase (d.rowLabel (pinWire d a).1),
    J8SourceMoment.genuineChild (localChild d e even g (outerAmplitude L) (F g))
      (fun p : LocalPin d g => sign p.1) (higher g) none (fun _ => 1)

omit [DecidableEq Packet] in
theorem publicSiblings_pos (e : RowEndpointSeating d) (even : Even L) (a : S)
    (F : OldTables d) (higher : RestArguments d) (sign : S → Bool) (hL : 0 < L)
    (sat : ∀ g v, ∃ x, LiteralPortCompiler.satisfied (F g v) x = true) :
    0 < (publicSiblings d e even a F higher sign).coeff 0 := by
  rw [publicSiblings, Polynomial.coeff_zero_prod]
  apply Finset.prod_pos
  intro g hg
  rw [physicalMarked_constant]
  apply J8SourceMoment.baselineMass_pos
  · exact amplitude_negative L hL even
  · exact J8SourceMoment.old_nonnegative _ _ _
  · exact J8SourceMoment.old_has_assignment _ _ _ (sat g)

/-- All model objects required by the old generic J8 decoder now have
literal physical definitions: source/address set, target/address set,
odd denominators, length-derived amplitude, and public sibling product. -/
theorem recover_physical_tile_exact (e : RowEndpointSeating d) (even : Even L) (a : S)
    (hL : 2 < L) (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a)
    (F : OldTables d) (higher : RestArguments d) (sign : S → Bool)
    (sat : ∀ g v, ∃ x, LiteralPortCompiler.satisfied (F g v) x = true)
    (tail : Fin (Fintype.card (PinTile d a)) → TargetPorts d a → ℚ[X]) :
    let gS := d.pinLabel a
    let gT := d.rowLabel (pinWire d a).1
    let pub := publicSiblings d e even a F higher sign
    let src := localChild d e even gS (outerAmplitude L) (F gS)
    let tgt := localChild d e even gT (outerAmplitude L) (F gT)
    let sites := fun i => tilePinInSource d (pinEnumeration d a i)
    let sh := fun p : LocalPin d gS => sign p.1
    let th := fun p : LocalPin d gT => sign p.1
    let other := fun b : Fin (Fintype.card (PinTile d a)) => tileBackground d a b
    let α := 2 * (L:ℚ)
    let scale := fun b : Fin (Fintype.card (PinTile d a)) =>
      J8SourceMoment.completedScale pub src tgt (groupedTargets d a) α (physicalDenominator d a) b
    let obs := fun b : Fin (Fintype.card (PinTile d a)) =>
      (J8SourceMoment.completedTile pub src tgt sh th (higher gS) (higher gT)
        sites (coordinates d a) other (groupedTargets d a) α (physicalDenominator d a) (tail b) b).coeff 1
    NativeMomentReconstruction.decodeBits (coordinates d a) scale
      (J8SourceMoment.nonpinBackground src other) obs =
          fun i => sign (pinEnumeration d a i).1 := by
  dsimp only
  apply J8SourceMoment.recover_from_exact_completed
  · exact coordinates_injective d a
  · exact publicSiblings_pos d e even a F higher sign (by omega) sat
  · exact amplitude_negative L (by omega) even
  · exact amplitude_negative L (by omega) even
  · exact J8SourceMoment.old_nonnegative _ _ _
  · exact J8SourceMoment.old_has_assignment _ _ _ (sat _)
  · exact J8SourceMoment.old_nonnegative _ _ _
  · exact J8SourceMoment.old_has_assignment _ _ _ (sat _)
  · intro _
    exact groupedTargets_nonempty d a off
  · have h : 0 < (L:ℚ) := by exact_mod_cast (show 0 < L by omega)
    positivity
  · intro b q hq
    exact physicalDenominator_pos d a even hL q hq

#print axioms physicalMarked_constant
#print axioms physicalMarked_sign_independent
#print axioms publicSiblings_pos
#print axioms recover_physical_tile_exact
end
end J8Physical.Relaxed