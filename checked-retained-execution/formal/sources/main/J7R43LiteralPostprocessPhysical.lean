import J7R43LiteralPostprocess
import J7R43LiteralDecoded
import J7R43LiteralNoDivision

/-! Use the same integer receipts for J7's literal Vandermonde
postprocessing. Its public rational background comes from the old
bounded column tables at zero pin contribution. No native answer
or general zero-probe theorem is added as an axiom. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open Polynomial J6R9Recursive J8Physical J8J9Grouped
open J9R19CompiledBits NativeMomentReconstruction
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option quotPrecheck false
set_option maxHeartbeats 4500000

variable {Packet R S V G : Type} {P : V→Type} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
variable (e : EndpointSeating d) (even : Even L)
variable (F : OldTables d) (sign : S→Bool)
variable {f : ℤ[X]} {ell : ℕ}

def publicBackgroundInteger (s : S) (b : ℕ) : ℤ :=
  integerSourceEvaluation d e even F (fun _=>false) s b

theorem literal_zero_background_correct (s : S) (hL : 0<L)
    (b : Fin (Fintype.card (PinTile d s)))
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F (d.pinLabel s) v) x=true) :
    (publicBackgroundInteger d e even F s b.val : ℚ) /
      (integerBaseline d e even F (d.pinLabel s) : ℚ) = actualPublicMoment d e even F s b.val := by
  unfold publicBackgroundInteger
  rw [← literal_source_no_division d e even hL F (fun _=>false) s b sat,
    actual_source_mass_formula d e even hL F (fun _=>false) s b sat,
    int_baseline_rat d e even hL F]
  have hm : NativeMomentReconstruction.moments (coordinates d s)
      (fun _ => (bitValue false : ℚ)) b = 0 := by
    simp [NativeMomentReconstruction.moments,NativeMomentReconstruction.bitValue,Matrix.vecMul, dotProduct]
  simp only [hm,add_zero]
  exact mul_div_cancel_left₀ _ (all_local_mass_positive d e even hL F _ sat).ne'

variable (s : S) (p : ℕ) (hf : f.Monic) (hell : 0<ell)
variable (base : Box f ell p) (obs : Fin (Fintype.card (PinTile d s)) → Box f ell p)
local notation "Z" => (readUnsigned p hf hell base : ℤ)
local notation "A" => (fun b : Fin (Fintype.card (PinTile d s)) =>
  (readUnsigned p hf hell (obs b) : ℤ))
local notation "B" => (fun b : Fin (Fintype.card (PinTile d s)) =>
  publicBackgroundInteger d e even F s b.val)

def nativeJ7Recovery (j : Fin (Fintype.card (PinTile d s))) : RecoveryRun :=
  recoverRun (coordinateInt d s) (literalDecoderInput Z B A) j

theorem native_J7_recovery_work (j : Fin (Fintype.card (PinTile d s))) :
    (nativeJ7Recovery d e even F s p hf hell base obs j).work ≤
      Fintype.card (PinTile d s)*(Fintype.card (PinTile d s)+1)+14*Fintype.card (PinTile d s)+2 :=
  literal_decoder_machine_work _ _ _ _ _

set_option maxHeartbeats 6200000 in
theorem native_J7_recovery_correct (j : Fin (Fintype.card (PinTile d s)))
    (idx : Wire R≃Fin M) (hL : 3≤L) (hM : L^3≤M)
    (capacity : L*Fintype.card Packet≤3*M)
    (sat : ∀ v, ∃ x, LiteralPortCompiler.satisfied (F (d.pinLabel s) v) x=true)
    (hp : 10*M≤p) (hF : 0<f.natDegree)
    (hbase : base = (J8J9Grouped.child d e even F sign (d.pinLabel s) none (fun _ => 1) : Box f ell p))
    (hobs : ∀ b, obs b = (J8J9Grouped.child d e even F sign (d.pinLabel s) none (feature d s b) : Box f ell p)) :
    (nativeJ7Recovery d e even F s p hf hell base obs j).answer =
      sign (pinEnumeration d s j).val := by
  have hm : 0<M := (pow_pos (by omega : 0<L) 3).trans_le hM
  have br := literal_native_baseline_fits d e even F sign s idx (by omega) hm capacity
    (d.pinLabel s) p hp
  have hz : Z = integerBaseline d e even F (d.pinLabel s) := by
    rw [hbase,readUnsigned_exact_int p (by omega) hf hF hell _ br.1 br.2]
    exact literal_baseline_no_division d e even (by omega) F sign _
  have mass : (0:ℚ)<(Z:ℚ) := by
    rw [hz,int_baseline_rat d e even (by omega) F]
    exact all_local_mass_positive d e even (by omega) F _ sat
  have hz0 : Z≠0 := by exact_mod_cast mass.ne'
  have cb : (fun b : Fin (Fintype.card (PinTile d s)) => (B b:ℚ)/(Z:ℚ)) =
      fun b => actualPublicMoment d e even F s b.val := by
    funext b
    rw [hz]
    exact literal_zero_background_correct d e even F s (by omega) b sat
  have H := literal_decoder_machine_correct (coordinateInt d s) Z B A j
    (coordinateInt_injective d s) hz0
  rw [funext (coordinateInt_exact d s),cb] at H
  simp only [Int.cast_natCast] at H
  exact H.trans (congrFun (decoded_from_actual_child_residues d e even F sign s idx hL hM capacity sat
    p hp hf hF hell base obs hbase hobs) j)

#print axioms publicBackgroundInteger
#print axioms literal_zero_background_correct
#print axioms native_J7_recovery_work
#print axioms native_J7_recovery_correct
end
end J7R43Literal
