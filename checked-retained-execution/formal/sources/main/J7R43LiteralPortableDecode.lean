import J7R43LiteralDecoded
import J7R43LiteralNoDivision

/-! The public J7 interface uses the actual finite tile's cardinality,
not a choice of proof-time finite enumeration dictionary. The casts
only identify the same order index, preserving its numeric value. -/
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

def toDecoderIndex (s : S) (j : Fin (Nat.card (PinTile d s))) :
    Fin (Fintype.card (PinTile d s)) :=
  Fin.cast (Nat.card_eq_fintype_card (α:=PinTile d s)) j

def fromDecoderIndex (s : S) (j : Fin (Fintype.card (PinTile d s))) :
    Fin (Nat.card (PinTile d s)) :=
  Fin.cast (Nat.card_eq_fintype_card (α:=PinTile d s)).symm j

def pinAtNaturalIndex (s : S) (j : Fin (Nat.card (PinTile d s))) : S :=
  (pinEnumeration d s (toDecoderIndex d s j)).val

theorem index_unchanged (s : S) (j : Fin (Nat.card (PinTile d s))) :
    (toDecoderIndex d s j).val=j.val := rfl

variable {f : ℤ[X]} {ell : ℕ}
variable (e : EndpointSeating d) (even : Even L) (F : OldTables d)

def decodeNativeNaturalOrders (s : S) (p : ℕ) (hf : f.Monic) (hell : 0<ell)
    (base : Box f ell p) (obs : Fin (Nat.card (PinTile d s)) → Box f ell p) :
    Fin (Nat.card (PinTile d s)) → Bool :=
  fun j =>
    NativeMomentReconstruction.decodeBits (coordinates d s)
      (fun _ => (readUnsigned p hf hell base : ℚ))
      (fun b => actualPublicMoment d e even F s b.val)
      (fun b => (readUnsigned p hf hell (obs (fromDecoderIndex d s b)) : ℚ))
      (toDecoderIndex d s j)

set_option maxHeartbeats 3100000 in
theorem decode_from_integer_evaluator_residues (sign : S→Bool)
    (s : S) (idx : Wire R≃Fin M) (hL : 3≤L) (hM : L^3≤M)
    (capacity : L*Fintype.card Packet≤3*M)
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F (d.pinLabel s) v) x=true)
    (p : ℕ) (hp : 10*M≤p) (hf : f.Monic) (hF : 0<f.natDegree) (hell : 0<ell)
    (base : Box f ell p) (obs : Fin (Nat.card (PinTile d s)) → Box f ell p)
    (hbase : base = (integerBaseline d e even F (d.pinLabel s) : Box f ell p))
    (hobs : ∀ b, obs b = (integerSourceEvaluation d e even F sign s b.val : Box f ell p)) :
    decodeNativeNaturalOrders d e even F s p hf hell base obs =
      fun j => sign (pinAtNaturalIndex d s j) := by
  have hp₀ : 0<L := by omega
  let D := Box f ell p
  have hb : base = (J8J9Grouped.child d e even F sign (d.pinLabel s) none (fun _ => 1) : D) :=
    hbase.trans (congrArg (fun n : ℤ => (n:D))
      (literal_baseline_no_division d e even hp₀ F sign (d.pinLabel s)).symm)
  have ho (b : Fin (Fintype.card (PinTile d s))) :
      obs (fromDecoderIndex d s b) =
        (J8J9Grouped.child d e even F sign (d.pinLabel s) none (feature d s b) : D) := by
    have h := hobs (fromDecoderIndex d s b)
    exact h.trans (congrArg (fun n : ℤ => (n:D))
      (literal_source_no_division d e even hp₀ F sign s b sat).symm)
  have H := decoded_from_actual_child_residues d e even F sign s idx hL hM capacity sat p hp
    hf hF hell base _ hb ho
  funext j
  exact congrFun H (toDecoderIndex d s j)

#print axioms index_unchanged
#print axioms decode_from_integer_evaluator_residues
end
end J7R43Literal