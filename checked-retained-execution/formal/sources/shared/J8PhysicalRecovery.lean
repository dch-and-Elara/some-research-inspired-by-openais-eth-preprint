import J8PhysicalKernel
import J8PhysicalMoments

/-!
One named physical tile, from the actual original packet addresses and old
literal tables to the exact rational sign decoder. This is the algebraic
readout after coefficient reconstruction, not an individual-probe cost claim.
-/

namespace J8Physical

open scoped Polynomial BigOperators Classical
open Polynomial

noncomputable section

variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

abbrev OldTables := (g : G) → (v : LocalColumn d g) → LiteralPortCompiler.CNF (LocalPort d v)

abbrev RestArguments :=
  (g : G) → ((LocalPin d g → Bool) × LocalBits d g) → LocalRow d g → Bool → ℚ[X]

abbrev TargetPorts (a : S) := LocalRow d (d.rowLabel (pinWire d a).1) × Bool

def physicalDenominator (a : S) (q : TargetPorts d a) : ℚ :=
  (((L:ℤ) - 1 - ((d.seat (pinWire d a)).2.val % 2 : ℕ) + (d.seat (q.1.1,q.2)).2.val : ℤ) : ℚ)

omit [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] [Fintype G] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem physicalDenominator_pos (a : S) (even : Even L) (hL : 2 < L)
    (q : TargetPorts d a) (hq : q ∈ groupedTargets d a) :
    0 < physicalDenominator d a q := by
  unfold physicalDenominator
  exact_mod_cast (groupedTargets_denom d a even hL hq).1

def publicSiblings (e : EndpointSeating d) (even : Even L) (a : S)
    (F : OldTables d) (higher : RestArguments d) (sign : S → Bool) : ℚ[X] :=
  ∏ g ∈ ((Finset.univ : Finset G).erase (d.pinLabel a)).erase (d.rowLabel (pinWire d a).1),
    J8SourceMoment.genuineChild (localChild d e even g (outerAmplitude L) (F g))
      (fun p : LocalPin d g => sign p.1) (higher g) none (fun _ => 1)

omit [DecidableEq Packet] in
theorem publicSiblings_pos (e : EndpointSeating d) (even : Even L) (a : S)
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
theorem recover_physical_tile_exact (e : EndpointSeating d) (even : Even L) (a : S)
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

#print axioms physicalDenominator_pos
#print axioms publicSiblings_pos
#print axioms recover_physical_tile_exact

end
end J8Physical
