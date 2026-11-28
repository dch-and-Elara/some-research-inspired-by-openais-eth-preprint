import V8NativeMessageN7Public
import V8NativeMessageN4PhysicalDensity
import V8PooledMenuGrid

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

/-! The actual signed centers of one retained coordinate, with no
missing sign, no probe dimension in the row message, and no abstract
choice of node count. -/
namespace V8NativeMessage.N8Literal
open scoped Classical BigOperators Polynomial
open Polynomial P1DyadicGrid J6ActiveRun J6ActiveSchedule J6R12Blueprint
open Paper5.D1Literal Paper5.HybridClosure V8NativeMessage.N6D

noncomputable section
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "a" => (J6ActiveRun.Shape.levelBits S 0)
local notation "u" => (J6ActiveRun.Shape.levelWidth S 0)
local notation "M" => Fintype.card (DWire F)
variable (d : N6PublicReady F reg (f:=f)) (i : rootKept F f)

abbrev Centers := {t : PublicCenter F reg f // padicValInt 2 t.val=i.val.val}
abbrev RowTape (q : ℕ) := Centers F reg i → TruncatedProbeMenu.NodeMessage q

theorem index_at_coordinate (t : Centers F reg i) :
    PublicIndex F reg f d t.val=i.val :=
  Fin.ext t.property

omit [DecidableEq W] in
theorem coordinate_retained : i.val.val<u :=
  (Finset.mem_filter.mp i.property).2

include d i in
theorem source_height_positive : 0<height M u := by
  have hi : i.val.val<u := coordinate_retained F i
  have hM : 0<M := Nat.zero_lt_of_lt d.active
  unfold height
  exact Nat.div_pos (by omega) (by omega)

def centerChart : Centers F reg i ≃ ↥(V8PooledMenu.shell a i.val.val) where
  toFun t :=
    let ht := Finset.mem_filter.mp t.val.property
    let hg := Finset.mem_erase.mp ht.1
    ⟨t.val.val,V8PooledMenu.mem_shell.mpr ⟨hg.2,hg.1,t.property⟩⟩
  invFun z := by
    let h := V8PooledMenu.mem_shell.mp z.property
    have hg := h.1
    have hz := h.2.1
    have hval := h.2.2
    have ht : 0<order M u z.val := by
      unfold order
      rw [hval]
      exact Nat.mul_pos (source_height_positive F reg d i) (Nat.sub_pos_of_lt (coordinate_retained F i))
    exact ⟨⟨z.val,Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hz,hg⟩,ht⟩⟩,hval⟩
  left_inv t := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

include d in
theorem center_card : Fintype.card (Centers F reg i)=2^a/2^i.val.val := by
  rw [Fintype.card_congr (centerChart F reg d i),Fintype.card_coe,V8PooledMenu.shell_card i.val.isLt.le]

def messageBits (q : ℕ) : ℕ := (2^a/2^i.val.val)*(q*(q+1)/2)

include d in
theorem exact_tape_size (q : ℕ) :
    Fintype.card (RowTape F reg i q)=2^messageBits F i q := by
  rw [Fintype.card_fun,TruncatedProbeMenu.node_message_card,center_card F reg d i,← pow_mul]
  unfold messageBits
  rw [Nat.mul_comm]

include d in
theorem coordinate_capacity_fits (t : Centers F reg i) {q : ℕ}
    (cap : q≤a+1-i.val.val) : q≤V8NativeMessage.N7.sitePrecision F reg t.val := by
  have h := V8NativeMessage.N7.root_low_fits F reg d t.val
  rw [index_at_coordinate F reg d i t] at h
  exact cap.trans h

#print axioms index_at_coordinate
#print axioms source_height_positive
#print axioms centerChart
#print axioms center_card
#print axioms exact_tape_size
#print axioms coordinate_capacity_fits
end
end V8NativeMessage.N8Literal
