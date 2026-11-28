import V8NativeMessageN7Public
import V8NativeMessageN7Shift

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1700000

/-! N7's actual zero-mode partial wiring on the same graph-fixed public
address. The output contains the original old table on every port, not
a newly supplied contraction or a sign-specific substitute layout. -/
namespace V8NativeMessage.N7
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
open J6R9PacketChild J6R10RowAffine J6R10PacketAssembly J6ActiveRun J6R12Blueprint J6R11Blueprint
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D
noncomputable section


section Shifted
variable {E A B G S : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] [CommRing S] {a : ℕ} {N : Network E A B} {f : ℤ[X]}

def evaluatedShift (P : PhysicalPacking N a G) (i : Fin a) (t : ℤ)
    (p : ℕ) (file : EntryFile f 1 N) (hf : f.Monic) (g : G)
    (ψ : Residue f 1 p→+*S) : S :=
  ∑ v : PhysicalState P i g, ψ (oldState P i g p file hf v) *
    ∏ k, ∏ r ∈ actualRows (childBlock P i) g k,
      LiteralPortCompiler.affine (groupBit (fun e=>P.seat e) (fun e=>P.seat e) P.mask i g v r)
        (shiftBase P i t g v r)

theorem child_shift_numeral (P : PhysicalPacking N a G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (mem : t∈grid a)
    (p : ℕ) (h₂ : (2:Residue f 1 p)^p=0) (z : Residue f 1 p)
    (file : EntryFile f 1 N) (hf : f.Monic) (g : G)
    (ψ : Residue f 1 p→+*S) (charTwo : (2:S)=0) :
    ψ (reduce p f 1 ((actualPacketHost P i ht hv p h₂ z file 0 g).contract hf)) =
      evaluatedShift P i t p file hf g ψ :=
  native_child_is_shift_at_parity P i ht hv mem p h₂ z file hf g ψ charTwo
end Shifted

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

theorem public_center_in_grid (t : PublicCenter F reg f) : t.val∈grid ((S).levelBits 0) := by
  have h := t.property
  change t.val∈((grid ((S).levelBits 0)).erase 0).filter _ at h
  exact Finset.mem_of_mem_erase (Finset.mem_filter.mp h).1

def shiftedPublicChild (hf : f.Monic) (σ : W→Bool) (t : PublicCenter F reg f) (g : Fin 64) :
    Residue f 1 1 :=
  let i := PublicIndex F reg f d t
  let p := sitePrecision F reg t
  let ψ := observe f p 1 (register_positive d t)
  let file := oldRowFile F reg f (4*Fintype.card W+1) σ
  evaluatedShift P i t.val p file hf g ψ

theorem original_zero_child_shift (hf : f.Monic) (σ : W→Bool)
    (x : PublicAddress F reg f P d) (zeroMode : x.2.2.1.val=0) :
    observe f (sitePrecision F reg x.1) 1 (register_positive d x.1)
      (publicReply F reg f P d hf σ x)=
    shiftedPublicChild F reg P d hf σ x.1 x.2.2.2 := by
  rw [public_word_is_literal F reg P d hf x σ]
  rw [zeroMode]
  unfold shiftedPublicChild
  exact child_shift_numeral P (PublicIndex F reg f d x.1)
    (centerNonzero x.1) rfl (public_center_in_grid F reg x.1) (sitePrecision F reg x.1)
    _ _ _ hf _ _ (by simpa only [pow_one] using J6R10Integral.box_two_nil 1 f 1)

theorem original_zero_whole_shift (hf : f.Monic) (σ : W→Bool)
    (x : PublicSlot F reg f P d) (zeroMode : x.2.2.val=0) :
    observe f (sitePrecision F reg x.1) 1 (register_positive d x.1) (wholePublic F reg P d hf σ x)=
      ∏ g : Fin 64,shiftedPublicChild F reg P d hf σ x.1 g := by
  rw [wholePublic,map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  exact original_zero_child_shift F reg P d hf σ ⟨x.1,x.2.1,x.2.2,g⟩ zeroMode

#print axioms public_center_in_grid
#print axioms original_zero_child_shift
#print axioms original_zero_whole_shift
end
end V8NativeMessage.N7
