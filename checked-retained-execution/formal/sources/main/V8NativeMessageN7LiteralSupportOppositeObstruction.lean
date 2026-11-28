import V8NativeMessageN7LiteralSupportOppositeUnit

/-! Opposite native completed root versus the genuine exterior-pair
target, at one fixed literal unit address across all sign words. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
open J6ActiveRun J6R12Blueprint J6R11Blueprint J1PPrinted
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 16000000
set_option maxRecDepth 2600
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (cubic : ∀v,GraphCutMoments.degree E v=3)
local notation "F" => (replacedEdges E cubic)
variable (loopless : ∀v,(v,v)∉E)
local notation "reg" => replaced_cubic E cubic loopless
variable {f : ℤ[X]}
local notation "SP" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "croot" => oldColumnRoot F reg f (fun _=>false)

theorem opposite_true_unit_cannot_equal_UD
    (P : ColumnPacking F reg (f:=f)) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin ((SP).levelBits 0))
    (hv : padicValInt 2 t.val=i.val) (unit : t.val=(-1))
    (β : J6R9PacketScopes.Mode i (registerPrecision SP croot t) P.mask →₀ ℕ)
    (hf : f.Monic) (hd : 0<f.natDegree) (e : E) :
    ∃ σ : TriVertex V→Bool,
    originalOppositeSlot F reg P d t i hv 0 β hf σ ≠
      UD E cubic (Residue f 1 (registerPrecision SP croot t)) σ := by
  let p := registerPrecision SP croot t
  have hp : 0<p := (Nat.zero_le _).trans_lt
    (original_high_precision_exceeds_four_edges F reg (show PublicCenter F reg f from t))
  have h1 : (1:ℤ)<(2:ℤ)^p := by
    calc
      (1:ℤ) = 2^0 := by norm_num
      _ < _ := pow_lt_pow_right₀ (by decide) hp
  have nz : (1:Residue f 1 p)≠0 := by
    intro zh
    have iv := (V8NativeMessage.N7HighBound.integer_box_zero_iff_of_height p hp f hf hd 1
      (by simpa only [abs_one] using h1)).mp (by simpa only [Int.cast_one] using zh)
    exact (by decide : (1:ℤ)≠0) iv
  by_cases zero : β=0
  · let σ := pairWord E cubic e false false
    refine ⟨σ,?_⟩
    rw [zero,show UD E cubic (Residue f 1 p) σ=0 by
      simp [σ,UD_one_pair,orValue]]
    exact literal_opposite_unit_has_full_support F reg P d t i hv unit hf hd σ
  · refine ⟨fun _=>true,?_⟩
    rw [literal_opposite_nonzero_mode_vanishes F reg P d t i hv β zero hf]
    have h : UD E cubic (Residue f 1 p) (fun _=>true)=1 := by
      unfold UD
      exact Finset.prod_eq_one (fun _ _=>rfl)
    rw [h]
    exact Ne.symm nz

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.opposite_true_unit_cannot_equal_UD
