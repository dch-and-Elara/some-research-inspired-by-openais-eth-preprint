import V8NativeMessageN7LiteralSupportOldRowNative
import V8NativeMessageN6DTarget

/-! On the original old-row four-clone host a single true completed
unit address cannot be the exterior-matching function on every sign. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
open J6ActiveRun J6R12Blueprint J6R11Blueprint J1PPrinted
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 2600
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀ v,GraphCutMoments.degree E v=3)
variable (loopless : ∀ v,(v,v)∉E)
local notation "F" => replacedEdges E baseCubic
local notation "hF" => replaced_cubic E baseCubic loopless
variable {f : ℤ[X]}

theorem old_row_true_unit_cannot_equal_UD
    (P : RootPacking (replacedEdges E baseCubic)
      (replaced_cubic E baseCubic loopless) f)
    (d : N6PublicReady F hF (f:=f)) (hf : f.Monic) (hd : 0<f.natDegree)
    (x : PublicSlot F hF f P d) (center : x.1.val=(-1))
    (z : siteProbe F hF d x.1 x.2.1=0) (e : E) :
    ∃ σ : TriVertex V→Bool,
      wholePublic F hF P d hf σ x ≠ UD E baseCubic (Residue f 1 (sitePrecision F hF x.1)) σ := by
  let p := sitePrecision F hF x.1
  have hp : 0<p := (Nat.zero_le _).trans_lt (original_high_precision_exceeds_four_edges F hF x.1)
  have h1 : (1:ℤ)<(2:ℤ)^p := by
    calc
      (1:ℤ)=2^0 := by norm_num
      _ < _ := pow_lt_pow_right₀ (by decide) hp
  have nz : (1:Residue f 1 p)≠0 := by
    intro zh
    have iv := (V8NativeMessage.N7HighBound.integer_box_zero_iff_of_height p hp f hf hd 1
      (by simpa only [abs_one] using h1)).mp (by simpa only [Int.cast_one] using zh)
    exact (by decide : (1:ℤ)≠0) iv
  have one : UD E baseCubic (Residue f 1 p) (fun _=>true)=1 := by
    unfold UD
    exact Finset.prod_eq_one (fun _ _=>rfl)
  by_cases mode : x.2.2.val=0
  · by_cases strong : oldRowSupported F hF P (-1) (fun _=>true)
    · refine ⟨fun _=>false,?_⟩
      have zero : UD E baseCubic (Residue f 1 p) (fun _=>false)=0 := by
        unfold UD
        exact Finset.prod_eq_zero (Finset.mem_univ e) rfl
      rw [zero]
      exact (original_old_row_unit_exact_support F hF P d hf hd _ x center z mode).mpr
        ⟨strong.1,fun _ h=>Bool.noConfusion h⟩
    · refine ⟨fun _=>true,?_⟩
      rw [one]
      have low : wholePublic F hF P d hf (fun _=>true) x=0 := by
        by_contra h
        exact strong ((original_old_row_unit_exact_support F hF P d hf hd _ x center z mode).mp h)
      rw [low]
      exact Ne.symm nz
  · refine ⟨fun _=>true,?_⟩
    rw [one,original_public_nonzero_at_zero F hF P d hf _ x mode z]
    exact Ne.symm nz

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.old_row_true_unit_cannot_equal_UD
