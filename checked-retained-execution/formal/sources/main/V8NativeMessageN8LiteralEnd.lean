import V8NativeMessageN8LiteralMenu
import V8NativeMessageN8LiteralRestriction

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3550000

/-! Original N8: an arbitrary function of the whole projected menu
requires one distinct side tape per matching row. This is not a time,
query-count, five-copy, or high-precision conclusion. -/
namespace V8NativeMessage.N8Literal
open scoped Classical BigOperators Polynomial
open Polynomial V8NativeMessage.N4 Paper5.D1Literal Paper5.HybridClosure
open J6R12Blueprint J6ActiveRun J6R10Repack P11FullPacking V8NativeMessage.N6D

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f)) (i : rootKept F f)
variable (q : ℕ) (cap : q≤(printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0+1-i.val.val)
variable (hf : f.Monic)
variable {γ : ℝ} (C : FourCut P i γ)

theorem actual_matching_receiver (hd : 0<f.natDegree) (x y : Fin C.m→Bool) :
    actualFixedMenu F reg P d i q cap hf (restriction C.pairs x y)=
      decodedMenu F reg P d i C.T q cap
        (rowMessage F reg P i C.T q (matchedRowWord C x)) (matchedColWord C y) := by
  rw [← original_matching_splice C x y]
  exact original_fixed_coordinate_payload F reg P d i C.T q cap hf hd
    (matchedRowWord C x) (matchedColWord C y)

/-- Even giving the receiver its own column word for free and b
additional row-only bits does not lower the displayed tape bound. -/
theorem original_N8_needs_bits (hd : 0<f.natDegree) {b : ℕ}
    (aux : (Fin C.m→Bool)→Fin b→Bool)
    (dec : (Fin C.m→Bool)→(Fin b→Bool)→FixedMenu F reg P d i q→ZMod 2)
    (correct : ∀ x y,
      dec y (aux x) (actualFixedMenu F reg P d i q cap hf (restriction C.pairs x y))=
        (nativeCount F reg (restriction C.pairs x y):ZMod 2)) :
    C.m≤messageBits F i q+b := by
  let sent (x : Fin C.m→Bool) : RowTape F reg i q × (Fin b→Bool) :=
    (rowMessage F reg P i C.T q (matchedRowWord C x),aux x)
  have hi : Function.Injective sent := by
    intro x x' h
    have hrow : rowMessage F reg P i C.T q (matchedRowWord C x)=
        rowMessage F reg P i C.T q (matchedRowWord C x') := congrArg Prod.fst h
    have haux : aux x=aux x' := congrArg Prod.snd h
    apply actual_count_rows_distinct C x x'
    intro y
    have hm : actualFixedMenu F reg P d i q cap hf (restriction C.pairs x y)=
        actualFixedMenu F reg P d i q cap hf (restriction C.pairs x' y) := by
      rw [actual_matching_receiver F reg P d i q cap hf C hd x y,
        actual_matching_receiver F reg P d i q cap hf C hd x' y,hrow]
    exact (correct x y).symm.trans ((congrArg₂ (dec y) haux hm).trans (correct x' y))
  have h := Fintype.card_le_of_injective sent hi
  rw [Fintype.card_prod,exact_tape_size F reg d i q] at h
  apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
  simpa [Fintype.card_fun,Fintype.card_bool,pow_add] using h

theorem original_N8_fails_if_small (hd : 0<f.natDegree) {b : ℕ}
    (aux : (Fin C.m→Bool)→Fin b→Bool)
    (dec : (Fin C.m→Bool)→(Fin b→Bool)→FixedMenu F reg P d i q→ZMod 2)
    (small : messageBits F i q+b<C.m) :
    ∃ x y, dec y (aux x) (actualFixedMenu F reg P d i q cap hf (restriction C.pairs x y))≠
      (nativeCount F reg (restriction C.pairs x y):ZMod 2) := by
  by_contra! h
  exact not_le_of_gt small (original_N8_needs_bits F reg P d i q cap hf C hd aux dec h)

theorem original_N8_no_aux (hd : 0<f.natDegree) (dec : FixedMenu F reg P d i q→ZMod 2)
    (correct : ∀ σ,dec (actualFixedMenu F reg P d i q cap hf σ)=(nativeCount F reg σ:ZMod 2)) :
    C.m≤messageBits F i q := by
  have h := original_N8_needs_bits F reg P d i q cap hf C hd
    (b:=0) (fun _ _=>false) (fun _ _=>dec)
    (fun x y=>correct (restriction C.pairs x y))
  simpa only [Nat.add_zero] using h

/-- Construct the source matching from the same old-row legal packing.
The chosen group union is not a new receiver parameter. -/
theorem original_N8_physical_cut (hd : 0<f.natDegree)
    (variance : varianceScore (actualCell P)≤
      2*(Nat.card (DWire F):ℚ)*J1PPrinted.sourceDelta (oldRowSize F))
    (γ : ℝ) (hγ : 0≤γ) (hE : V8NativeMessage.C2Physical.ExpansionOn (storageGraph F) γ)
    (hloop : ∀ v,(v,v)∉F) (dec : FixedMenu F reg P d i q→ZMod 2)
    (correct : ∀ σ,dec (actualFixedMenu F reg P d i q cap hf σ)=(nativeCount F reg σ:ZMod 2)) :
    γ*(Fintype.card W:ℝ)≤68*(messageBits F i q:ℝ) := by
  obtain ⟨C⟩ := four_cut_from_pack P d variance i γ hγ hE hloop
  have h := original_N8_no_aux F reg P d i q cap hf C hd dec correct
  exact C.match_budget.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by norm_num))

#print axioms actual_matching_receiver
#print axioms original_N8_needs_bits
#print axioms original_N8_fails_if_small
#print axioms original_N8_no_aux
#print axioms original_N8_physical_cut
end
end V8NativeMessage.N8Literal
