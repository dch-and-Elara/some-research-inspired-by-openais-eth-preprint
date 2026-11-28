import V8NativeMessageGroups
import V8NativeMessageN4PhysicalDensity

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

/-! Original four-copy N8 payload on the same old-row ownership cut as
N4. There is no five-copy availability switch or separate source
polynomial to supply. -/
namespace V8NativeMessage.N8Literal
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9PacketScopes
open Paper5.D1Literal Paper5.HybridClosure V8NativeMessage.N4

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {reg : ∀v,GraphCutMoments.degree F v=3}
variable {f : ℤ[X]}
variable (P : RootPacking F reg f) (i : rootKept F f) (T : Finset (Fin 64))

abbrev RowWord := {v : W // pinGroup P i v∈T}→Bool
abbrev ColWord := {v : W // pinGroup P i v∉T}→Bool

def rowFill (x : RowWord P i T) (v : W) : Bool :=
  if hv : pinGroup P i v∈T then x ⟨v,hv⟩ else true
def colFill (y : ColWord P i T) (v : W) : Bool :=
  if hv : pinGroup P i v∈T then true else y ⟨v,hv⟩
def mergeSigns (x : RowWord P i T) (y : ColWord P i T) (v : W) : Bool :=
  if hv : pinGroup P i v∈T then x ⟨v,hv⟩ else y ⟨v,hv⟩

theorem oldRowTruth_at_pin_only (σ τ : W→Bool) (u : DOld F ⊕ MainClonedCNF.Port F)
    (x : ParentPorts (dNetwork F reg) u→Bool)
    (same : ∀ v : W, u=.inl (.inr (.inl v)) → σ v=τ v) :
    oldRowTruth F reg σ u x=oldRowTruth F reg τ u x := by
  rcases u with (k|w|e|c)|e
  · rfl
  · simp only [oldRowTruth,same w rfl]
  · rfl
  · rfl
  · rfl

theorem original_part_local (t : ℤ) (σ τ : W→Bool)
    (same : ∀ v, pinGroup P i v∈T → σ v=τ v) :
    V8NativeMessage.partPoly P i.val t T (oldRowTruth F reg σ)=
      V8NativeMessage.partPoly P i.val t T (oldRowTruth F reg τ) := by
  apply V8NativeMessage.part_local
  intro u hu q
  apply oldRowTruth_at_pin_only
  intro w hw
  apply same w
  rw [hw] at hu
  exact hu

def rowPolynomial (t : ℤ) (x : RowWord P i T) : TwoLocal[X] :=
  V8NativeMessage.partPoly P i.val t T (oldRowTruth F reg (rowFill P i T x))
def colPolynomial (t : ℤ) (y : ColWord P i T) : TwoLocal[X] :=
  V8NativeMessage.partPoly P i.val t Tᶜ (oldRowTruth F reg (colFill P i T y))

theorem exact_side_split (t : ℤ) (x : RowWord P i T) (y : ColWord P i T) :
    V8PooledMenu.wholeScaled P i.val t (oldRowTruth F reg (mergeSigns P i T x y)) =
      rowPolynomial P i T t x * colPolynomial P i T t y := by
  rw [V8NativeMessage.whole_split P i.val t T]
  apply congrArg₂ (·*·)
  · apply original_part_local P i T
    intro w h
    simp only [mergeSigns,rowFill,dif_pos h]
  · apply original_part_local P i Tᶜ
    intro w h
    have hn := Finset.mem_compl.mp h
    simp only [mergeSigns,colFill,dif_neg hn]

#print axioms oldRowTruth_at_pin_only
#print axioms original_part_local
#print axioms exact_side_split
end
end V8NativeMessage.N8Literal
