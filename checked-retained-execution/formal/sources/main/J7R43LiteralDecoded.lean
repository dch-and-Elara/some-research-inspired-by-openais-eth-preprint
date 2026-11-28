import J7R43LiteralDecode
import J7R43LiteralReadout
import J7R43LiteralBoundSum

/-! The integer precision bound enables an actual finite readout of the
one-child observations, before rational Vandermonde division. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open Polynomial J6R9Recursive J8Physical J8J9Grouped
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type} {P : V→Type} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
variable (e : EndpointSeating d) (even : Even L)
variable (F : OldTables d) (sign : S→Bool)
variable {f : ℤ[X]} {ell : ℕ}

set_option maxHeartbeats 2200000 in
theorem decoded_from_actual_child_residues
    (s : S) (idx : Wire R≃Fin M) (hL : 3≤L) (hM : L^3≤M)
    (capacity : L*Fintype.card Packet≤3*M)
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F (d.pinLabel s) v) x=true)
    (p : ℕ) (hp : 10*M≤p) (hf : f.Monic) (hF : 0<f.natDegree) (hell : 0<ell)
    (base : Box f ell p) (obs : Fin (Fintype.card (PinTile d s)) → Box f ell p)
    (hbase : base = (J8J9Grouped.child d e even F sign (d.pinLabel s) none (fun _ => 1) : Box f ell p))
    (hobs : ∀ b, obs b = (J8J9Grouped.child d e even F sign (d.pinLabel s) none (feature d s b) : Box f ell p)) :
    NativeMomentReconstruction.decodeBits (coordinates d s)
      (fun _ => (readUnsigned p hf hell base : ℚ))
      (fun b => actualPublicMoment d e even F s b.val)
      (fun b => (readUnsigned p hf hell (obs b) : ℚ)) =
        fun j => sign (pinEnumeration d s j).val := by
  have hM' : 0<M := (pow_pos (by omega : 0<L) 3).trans_le hM
  have hBaseRange := literal_native_baseline_fits d e even F sign s idx (by omega) hM' capacity
    (d.pinLabel s) p hp
  have hZ : (readUnsigned p hf hell base : ℚ) =
      (J8J9Grouped.child d e even F sign (d.pinLabel s) none (fun _ => 1) : ℚ) := by
    have h : (readUnsigned p hf hell base : ℤ) =
        J8J9Grouped.child d e even F sign (d.pinLabel s) none (fun _ => 1) := by
      rw [hbase]
      exact readUnsigned_exact_int p (by omega) hf hF hell _ hBaseRange.1 hBaseRange.2
    exact_mod_cast h
  have hSynced (b : Fin (Fintype.card (PinTile d s))) :
      (readUnsigned p hf hell (obs b) : ℚ) =
        (J8J9Grouped.child d e even F sign (d.pinLabel s) none (feature d s b) : ℚ) := by
    have hBound := literal_native_source_fits d e even F sign s idx hL hM capacity b p hp
    have h : (readUnsigned p hf hell (obs b) : ℤ) =
        J8J9Grouped.child d e even F sign (d.pinLabel s) none (feature d s b) := by
      rw [hobs b]
      exact readUnsigned_exact_int p (by omega) hf hF hell _ hBound.1 hBound.2
    exact_mod_cast h
  simp only [hZ,hSynced]
  exact decode_literal_integer_tile d e even (by omega) F sign s sat

#print axioms decoded_from_actual_child_residues
end
end J7R43Literal