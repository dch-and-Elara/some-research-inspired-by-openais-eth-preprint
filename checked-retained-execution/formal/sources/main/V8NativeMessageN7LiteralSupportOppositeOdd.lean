import V8NativeMessageN7LiteralSupportOddRead
import V8NativeMessageN7LiteralSupportColumnPositive
import V8NativeMessageN7LiteralSupportOddSign

/-! Both the exact rational (all odd centres) and the original opposite
native support (within the receiver's explicit finite height window). -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial DenominatorBudget P1DyadicGrid P11FullPacking J6R10Repack J6R9Recursive
open J6R9PacketCoeff J6ActiveRun J6R12Blueprint J6R11Blueprint J1PPrinted
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14000000
set_option maxRecDepth 2600
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)

theorem old_column_odd_exact_has_full_support {a : ℕ}
    (P : PhysicalPacking (oldColumnNetwork F reg) a (Fin 64))
    (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (mem : t∈grid a) (odd : Odd t) (σ : W→Bool) :
    0<twoLocalRat (exactZero P i t (oldColumnTruth F reg σ)) := by
  rw [exactZero,full_signed_root_is_zero_polynomial,map_signed_root,rho_rat mem]
  exact true_old_columns_strictly_positive F reg P ht i hv (odd_centres_have_negative_actual_scalar mem odd) σ

variable {f : ℤ[X]}
local notation "SP" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "root" => oldColumnRoot F reg f (fun _=>false)
local notation "a" => (J6ActiveRun.Shape.levelBits (SP) 0)
local notation "u" => (J6ActiveRun.Shape.levelWidth (SP) 0)
local notation "M" => Fintype.card (DWire F)

theorem original_opposite_small_odd_has_full_support
    (P : ColumnPacking F reg (f:=f)) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin a)
    (hv : padicValInt 2 t.val=i.val) (odd : Odd t.val)
    (small : clearedExponent a t.val*u<24*2^a)
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) :
    originalOppositeSlot F reg P d t i hv 0 0 hf σ≠0 := by
  let p := registerPrecision SP root t
  have hm : 0<M := (Nat.zero_le _).trans_lt d.active
  obtain ⟨_,budget⟩ := actual_odd_site_has_precision_budget F reg (show PublicCenter F reg f from t) odd
  have strict : M*clearedExponent a t.val*u<p*u := by
    calc
      _ = M*(clearedExponent a t.val*u) := by ring
      _ < M*(24*2^a) := Nat.mul_lt_mul_of_pos_left small hm
      _ = 24*M*2^a := by ring
      _ ≤ p*u := budget
  have room : M*clearedExponent a t.val<p := Nat.lt_of_mul_lt_mul_right strict
  have mem := V8NativeMessage.N7.public_center_in_grid F reg (show PublicCenter F reg f from t)
  have hp : 0<p := (Nat.zero_le _).trans_lt room
  intro z
  have h := (finite_zero_iff_exact_same_rational P (oldColumnTruth F reg σ) i
    (centerNonzero t) hv mem (4*Fintype.card W+1) p (by omega) hp hf hd room).mp z
  have pos := old_column_odd_exact_has_full_support F reg P i (centerNonzero t) hv mem odd σ
  rw [h,map_zero] at pos
  exact (lt_irrefl _ pos)

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.old_column_odd_exact_has_full_support
#print axioms V8NativeMessage.N7LiteralSupport.original_opposite_small_odd_has_full_support
