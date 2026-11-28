import V8NativeMessageN8PrescribedSupport

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000
set_option maxRecDepth 2450

/-! The unchanged four-copy OR witness, now on every permitted
prescribed binary-address chart of the one fixed retained coordinate. -/
namespace V8NativeMessage.N8Prescribed
open scoped Classical BigOperators Polynomial
open Polynomial V8NativeMessage.N4 Paper5.D1Literal Paper5.HybridClosure Paper5.HybridClosure.Printed
open J6R12Blueprint J6ActiveRun J6R10Repack P11FullPacking V8NativeMessage.N6D J1PPrinted
open V8NativeMessage.N8Literal

noncomputable section
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f)) (i : rootKept F f)
variable (B : Chart (f:=f) F reg i)
variable (q : ℕ) (cap : q≤(printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0+1-i.val.val)
variable (hf : f.Monic)

section Match
variable {γ : ℝ} (C : FourCut P i γ)

theorem matching_receiver_prescribed (hd : 0<f.natDegree) (x y : Fin C.m→Bool) :
    actualPrescribedMenu (f:=f) F reg P d i B q cap hf (restriction C.pairs x y)=
      decodePrescribed (f:=f) F reg P d i B q cap C.T
        (rowMessage (f:=f) F reg P i C.T q (matchedRowWord C x)) (matchedColWord C y) := by
  rw [← original_matching_splice C x y]
  exact same_base_scalar_tape_for_prescribed (f:=f) F reg P d i B q cap C.T hf hd
    (matchedRowWord C x) (matchedColWord C y)

theorem N8_prescribed_needs_bits (hd : 0<f.natDegree) {b : ℕ}
    (aux : (Fin C.m→Bool)→Fin b→Bool)
    (dec : (Fin C.m→Bool)→(Fin b→Bool)→FixedMenu (f:=f) F reg P d i q→ZMod 2)
    (correct : ∀ x y, dec y (aux x)
      (actualPrescribedMenu (f:=f) F reg P d i B q cap hf (restriction C.pairs x y))=
        (nativeCount F reg (restriction C.pairs x y):ZMod 2)) :
    C.m≤messageBits F i q+b := by
  let sent (x : Fin C.m→Bool) : RowTape (f:=f) F reg i q × (Fin b→Bool) :=
    (rowMessage (f:=f) F reg P i C.T q (matchedRowWord C x),aux x)
  have hi : Function.Injective sent := by
    intro x x' e
    have hx : rowMessage (f:=f) F reg P i C.T q (matchedRowWord C x)=
        rowMessage (f:=f) F reg P i C.T q (matchedRowWord C x') := congrArg Prod.fst e
    have ha : aux x=aux x' := congrArg Prod.snd e
    apply actual_count_rows_distinct C x x'
    intro y
    have hr : actualPrescribedMenu (f:=f) F reg P d i B q cap hf (restriction C.pairs x y)=
      actualPrescribedMenu (f:=f) F reg P d i B q cap hf (restriction C.pairs x' y) := by
      rw [matching_receiver_prescribed (f:=f) F reg P d i B q cap hf C hd x y,
        matching_receiver_prescribed (f:=f) F reg P d i B q cap hf C hd x' y,hx]
    exact (correct x y).symm.trans ((congrArg₂ (dec y) ha hr).trans (correct x' y))
  have h := Fintype.card_le_of_injective sent hi
  rw [Fintype.card_prod,exact_tape_size (f:=f) F reg d i q] at h
  apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
  simpa [Fintype.card_fun,Fintype.card_bool,pow_add] using h
end Match

theorem prescribed_physical_cut (hd : 0<f.natDegree)
    (variance : varianceScore (actualCell P)≤2*(Nat.card (DWire F):ℚ)*sourceDelta (oldRowSize F))
    (γ : ℝ) (hγ : 0≤γ) (hE : V8NativeMessage.C2Physical.ExpansionOn (storageGraph F) γ)
    (hloop : ∀ v,(v,v)∉F) (dec : FixedMenu (f:=f) F reg P d i q→ZMod 2)
    (correct : ∀ σ,dec (actualPrescribedMenu (f:=f) F reg P d i B q cap hf σ)=(nativeCount F reg σ:ZMod 2)) :
    γ*(Fintype.card W:ℝ)≤68*(messageBits F i q:ℝ) := by
  obtain ⟨C⟩ := four_cut_from_pack P d variance i γ hγ hE hloop
  have h := N8_prescribed_needs_bits (f:=f) F reg P d i B q cap hf C hd
      (b:=0) (fun _ _=>false) (fun _ _=>dec) (fun x y=>correct (restriction C.pairs x y))
  have h' : C.m≤messageBits F i q := by simpa only [Nat.add_zero] using h
  exact C.match_budget.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast h') (by norm_num))

theorem N8_prescribed_printed_failure (γ : ℝ) (hγ : 0<γ) :
    ∃ n₀ : ℕ, ∀ (U : Type) [Fintype U] [DecidableEq U]
      (E : Finset (U×U)) (cubic : ∀ v,GraphCutMoments.degree E v=3) (f₀ : ℤ[X]),
      n₀≤Fintype.card U →
      ∀ (P₀ : RootPacking E cubic f₀) (d₀ : N6PublicReady E cubic (f:=f₀)) (i₀ : rootKept E f₀)
        (B₀ : Chart (f:=f₀) E cubic i₀)
        (p : ℕ) (low : p≤(printedParams (f:=f₀) (ell:=1) (oldRowSize E)).levelBits 0+1-i₀.val.val)
        (hmonic : f₀.Monic) (_hd : 0<f₀.natDegree),
        varianceScore (actualCell P₀)≤2*(Nat.card (DWire E):ℚ)*sourceDelta (oldRowSize E) →
        V8NativeMessage.C2Physical.ExpansionOn (storageGraph E) γ →
        (∀ v,(v,v)∉E) →
        ∀ dec : FixedMenu (f:=f₀) E cubic P₀ d₀ i₀ p→ZMod 2,
        ∃ σ, dec (actualPrescribedMenu (f:=f₀) E cubic P₀ d₀ i₀ B₀ p low hmonic σ)≠(nativeCount E cubic σ:ZMod 2) := by
  obtain ⟨n₀,hs⟩ := source_cutoff_exists γ hγ
  refine ⟨n₀,?_⟩
  intro U _ _ E cubic f₀ hN P₀ d₀ i₀ B₀ p low hm hd variance hE hloop dec
  by_contra! hgood
  have hcap := low.trans (le_of_eq (congrArg (fun a : ℕ=>a+1-i₀.val.val)
    (actual_printed_a (f:=f₀) E cubic)))
  have hb := hs (Fintype.card U) i₀.val.val p hN hcap
  rw [← exact_printed_tape (f:=f₀) E cubic i₀ p] at hb
  exact not_le_of_gt hb
    (prescribed_physical_cut (f:=f₀) E cubic P₀ d₀ i₀ B₀ p low hm hd variance γ hγ.le hE hloop dec hgood)

#print axioms matching_receiver_prescribed
#print axioms N8_prescribed_needs_bits
#print axioms prescribed_physical_cut
#print axioms N8_prescribed_printed_failure
end
end V8NativeMessage.N8Prescribed