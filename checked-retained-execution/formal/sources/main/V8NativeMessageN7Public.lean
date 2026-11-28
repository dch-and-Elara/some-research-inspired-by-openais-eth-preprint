import V8NativeMessageN7Kernel
import V8NativeMessageN6DPrinted

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 2400

/-! Scale and probe the original Appendix D public *whole slot*. This
uses the unchanged old-row file and actual legal high mode, followed by
the literal coefficient and V quotient projection. No five-copy source
data are used; the underlying kernel theorem is graph independent. -/
namespace V8NativeMessage.N7
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
open J6ActiveRun J6R12Blueprint J6R10Reachable J1PPrinted
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "r*" => (oldRowRoot F reg f (fun _=>false))

variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

abbrev sitePrecision (t : PublicCenter F reg f) := registerPrecision S r* t
abbrev siteProbe (t : PublicCenter F reg f) (z : PublicProbe F reg f) :=
  sampleNode S f 1 r* d.fit t z

/-- Real born-old tables are unchanged. The high child reply is exactly
at its public center, public probe and public mode. -/
def wholePublic (hf : f.Monic) (σ : W→Bool) (x : PublicSlot F reg f P d) :
    Residue f 1 (sitePrecision F reg x.1) :=
  ∏ g : Fin 64, publicReply F reg f P d hf σ ⟨x.1,x.2.1,x.2.2,g⟩

theorem publicSlot_is_literal (hf : f.Monic) (σ : W→Bool) (x : PublicSlot F reg f P d) :
    wholePublic F reg P d hf σ x =
      V8PooledMenu.slot P (PublicIndex F reg f d x.1) (centerNonzero x.1) rfl
        (sitePrecision F reg x.1) (J6R10Integral.box_two_nil (sitePrecision F reg x.1) f 1)
        (siteProbe F reg d x.1 x.2.1)
        (oldRowFile F reg f (4*Fintype.card W+1) σ) hf x.2.2.val := by
  unfold wholePublic V8PooledMenu.slot
  apply Finset.prod_congr rfl
  intro g _
  exact public_word_is_literal F reg P d hf ⟨x.1,x.2.1,x.2.2,g⟩ σ

theorem root_low_fits (t : PublicCenter F reg f) :
    (S).levelBits 0+1-(PublicIndex F reg f d t).val≤sitePrecision F reg t := by
  have hp : 0 < Fintype.card (DWire F) :=
    lt_of_le_of_lt (Nat.zero_le _) d.active
  let a := (S).levelBits 0
  let M := Fintype.card (DWire F)
  have hM : 0<8*M := Nat.mul_pos (by decide) hp
  calc
    _ ≤ a+1 := Nat.sub_le _ _
    _ ≤ 8*M*(a+1) := Nat.le_mul_of_pos_left _ hM
    _ ≤ sitePrecision F reg t := by
      change _≤J9PrintedSchedule.precision (4*Fintype.card W+1)
        (J6ActiveSchedule.height M ((S).levelWidth 0)) (2^a/2^padicValInt 2 t.val) M a
      unfold J9PrintedSchedule.precision
      omega

/-- Actual receiving quotient: the high mode and probe are unchanged. -/
def observe (f : ℤ[X]) (p q : ℕ) (h : q≤p) : Residue f 1 p→+*Residue f 1 q :=
  adjoinMap (NativeProbeRing.reduceScalar q p h f) (X^1) (X^1) (by simp)

theorem original_public_nonzero_erased (hf : f.Monic) (σ : W→Bool) (x : PublicSlot F reg f P d)
    (nonzero : x.2.2.val≠0) {q : ℕ}
    (low : q≤(S).levelBits 0+1-(PublicIndex F reg f d x.1).val) :
    observe f (sitePrecision F reg x.1) q (low.trans (root_low_fits F reg d x.1))
      (wholePublic F reg P d hf σ x)=0 := by
  rw [publicSlot_is_literal]
  exact V8PooledMenu.projected_nonzero_slot P (PublicIndex F reg f d x.1)
    (centerNonzero x.1) rfl (sitePrecision F reg x.1) _ _ _ hf x.2.2.val nonzero _
    low (J6R10Integral.box_two_nil q f 1)

theorem original_public_nonzero_at_zero (hf : f.Monic) (σ : W→Bool) (x : PublicSlot F reg f P d)
    (nonzero : x.2.2.val≠0) (isZero : siteProbe F reg d x.1 x.2.1=0) :
    wholePublic F reg P d hf σ x=0 := by
  rw [publicSlot_is_literal,isZero]
  exact native_zero_probe_nonzero_mode P (PublicIndex F reg f d x.1)
    (centerNonzero x.1) rfl (sitePrecision F reg x.1) _ _ hf x.2.2.val nonzero

theorem original_public_zero_all_probes (hf : f.Monic) (σ : W→Bool)
    (t : PublicCenter F reg f) (z z' : PublicProbe F reg f) (β : PublicMenu F reg f P d t)
    (isZero : β.val=0) :
    let ψ := observe f (sitePrecision F reg t) 1 (register_positive d t)
    ψ (wholePublic F reg P d hf σ ⟨t,z,β⟩) = ψ (wholePublic F reg P d hf σ ⟨t,z',β⟩) := by
  dsimp only
  rw [publicSlot_is_literal,publicSlot_is_literal]
  change observe f _ 1 _ (V8PooledMenu.slot P (PublicIndex F reg f d t) (centerNonzero t)
      rfl (sitePrecision F reg t) _ (siteProbe F reg d t z) _ hf β.val)=
    observe f _ 1 _ (V8PooledMenu.slot P (PublicIndex F reg f d t) (centerNonzero t)
      rfl (sitePrecision F reg t) _ (siteProbe F reg d t z') _ hf β.val)
  rw [isZero]
  exact zero_mode_same_probe_mod_two P (PublicIndex F reg f d t) (centerNonzero t)
    rfl (sitePrecision F reg t) _ _ hf _ _ _
    (by simpa only [pow_one] using J6R10Integral.box_two_nil 1 f 1)

#print axioms publicSlot_is_literal
#print axioms root_low_fits
#print axioms original_public_nonzero_erased
#print axioms original_public_nonzero_at_zero
#print axioms original_public_zero_all_probes

end
end V8NativeMessage.N7
