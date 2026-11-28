import V8NativeMessageN7PublicShift

/-! Unprojected value of a real zero-probe completed slot. Parity is
not used in this step, and an address roster is not assumed to contain
zero. The same binary host tables and creation precision are kept. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
open J6R9PacketScopes J6ActiveRun J6R12Blueprint J6R11Blueprint
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
set_option maxRecDepth 2000
noncomputable section

section General
variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B} {f : ℤ[X]}

def exactZero (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool) : TwoLocal :=
  (V8PooledMenu.wholeScaled P i t flags).eval 0

theorem actual_zero_slot_is_reduction
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool)
    (p₀ p : ℕ) (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree) :
    V8PooledMenu.slot P i ht hv p (J6R10Integral.box_two_nil p f 1) 0
      (V8PooledMenu.binaryFile f p₀ flags) hf 0 =
    J6ZeroTransport.reduceAt p (J6R10Integral.box_two_nil p f 1) (exactZero P i t flags) := by
  let e : TwoLocal→+*Residue f 1 p :=
    J6ZeroTransport.reduceAt p (J6R10Integral.box_two_nil p f 1)
  let I := RingHom.id (Residue f 1 p)
  have s := V8PooledMenu.projected_zero_slot P i ht hv p
    (J6R10Integral.box_two_nil p f 1) 0 (V8PooledMenu.binaryFile f p₀ flags) hf I
  have eval := V8PooledMenu.wholeScaled_eval P i t flags p₀ hp₀ hf hd p
    (J6R10Integral.box_two_nil p f 1) 0 I
  change (V8PooledMenu.wholeScaled P i t flags).eval₂ (I.comp e) (2*I 0)=_ at eval
  rw [map_zero,mul_zero,RingHom.id_comp] at eval
  calc
    _ = _ := s
    _ = (V8PooledMenu.wholeScaled P i t flags).eval₂ e 0 := eval.symm
    _ = _ := by simp only [exactZero,Polynomial.eval₂_at_zero,Polynomial.coeff_zero_eq_eval_zero,e]

end General

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

/-- Same original R12 public completed value at its printed high p_t.
A supplied zero probe is required, not deduced for an arbitrary menu. -/
theorem original_public_full_zero_probe
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) (x : PublicSlot F reg f P d)
    (isZero : siteProbe F reg d x.1 x.2.1=0) :
    wholePublic F reg P d hf σ x =
      if x.2.2.val=0 then
        J6ZeroTransport.reduceAt (sitePrecision F reg x.1)
          (J6R10Integral.box_two_nil (sitePrecision F reg x.1) f 1)
          (exactZero P (PublicIndex F reg f d x.1) x.1.val (oldRowTruth F reg σ))
      else 0 := by
  by_cases mode : x.2.2.val=0
  · rw [if_pos mode,publicSlot_is_literal,mode,isZero]
    exact actual_zero_slot_is_reduction P (PublicIndex F reg f d x.1) (centerNonzero x.1) rfl
      (oldRowTruth F reg σ) (4*Fintype.card W+1) (sitePrecision F reg x.1) (by omega) hf hd
  · rw [if_neg mode]
    exact original_public_nonzero_at_zero F reg P d hf σ x mode isZero

theorem original_high_precision_exceeds_four_edges (t : PublicCenter F reg f) :
    4*Fintype.card (DWire F)<sitePrecision F reg t := by
  let M := Fintype.card (DWire F)
  let S := printedParams (f:=f) (ell:=1) (oldRowSize F)
  change 4*M<J9PrintedSchedule.precision (4*Fintype.card W+1)
    (J6ActiveSchedule.height M (S.levelWidth 0))
    (2^S.levelBits 0/2^padicValInt 2 t.val) M (S.levelBits 0)
  have lo : 8*M≤8*M*(S.levelBits 0+1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold J9PrintedSchedule.precision
  omega

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.actual_zero_slot_is_reduction
#print axioms V8NativeMessage.N7LiteralSupport.original_public_full_zero_probe
#print axioms V8NativeMessage.N7LiteralSupport.original_high_precision_exceeds_four_edges
