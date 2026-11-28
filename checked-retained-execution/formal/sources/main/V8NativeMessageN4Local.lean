import V8NativeMessageN4PhysicalTarget
import P5D1LiteralTerms

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3700000

/-! At the chosen original D1 coordinate separate child lifts really
depend just on the signed unary vertices in that child's old-row group.
The generic N4 model may use any functions of precisely those bits. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open Paper5.D1Literal Paper5.HybridClosure J6R12Blueprint J6ActiveRun J6R9Recursive J1PPrinted
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)}
variable {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]}
variable {P : RootPacking F reg f} {i : rootKept F f}
variable {A : Type*} [Field A] [LinearOrder A] {γ : A} (C : FourCut P i γ)

def leftSide (v : W) : Bool := decide (pinGroup P i v∈C.T)

def leftWord (x : Fin C.m→Bool) : W→Bool := restriction C.pairs x (fun _ => true)

def rightWord (y : Fin C.m→Bool) : W→Bool := restriction C.pairs (fun _ => true) y

theorem restriction_splice (x y : Fin C.m→Bool) :
    (fun v => if leftSide C v then leftWord C x v else rightWord C y v)=
      restriction C.pairs x y := by
  funext v
  by_cases hv : v∈Set.range C.pairs.seat
  · obtain ⟨⟨j,b⟩,rfl⟩ := hv
    cases b
    · simp only [leftSide,C.left j,decide_true,if_true,leftWord,restriction_on,Bool.false_eq_true,if_false]
    · simp only [leftSide,C.right j,decide_false,Bool.false_eq_true,if_false,rightWord,restriction_on,if_true]
  · have hl : leftWord C x v=true := restriction_off _ _ _ _ hv
    have hr : rightWord C y v=true := restriction_off _ _ _ _ hv
    rw [restriction_off _ _ _ _ hv,hl,hr,ite_self]

abbrev LocalFactors (P : RootPacking F reg f) (i : rootKept F f) (R : Type*) :=
  (g : Fin 64) → (Pins P i g→Bool) → R

variable {R : Type*} [CommMonoid R]

def nativeD (D : LocalFactors P i R) (σ : W→Bool) : R :=
  ∏ g, D g (fun v => σ v.val)

def leftD (D : LocalFactors P i R) (x : Fin C.m→Bool) : R :=
  ∏ g ∈ C.T, D g (fun v => leftWord C x v.val)

def rightD (D : LocalFactors P i R) (y : Fin C.m→Bool) : R :=
  ∏ g ∈ C.Tᶜ, D g (fun v => rightWord C y v.val)

theorem true_D_cut (D : LocalFactors P i R) (x y : Fin C.m→Bool) :
    nativeD D (restriction C.pairs x y)=leftD C D x*rightD C D y := by
  rw [nativeD, ← Finset.prod_mul_prod_compl C.T]
  unfold leftD rightD
  congr 1
  · apply Finset.prod_congr rfl
    intro g hg
    apply congrArg (D g)
    funext w
    rw [← restriction_splice C x y]
    have ht : pinGroup P i w.val∈C.T := w.property.symm ▸ hg
    simp [leftSide,ht]
  · apply Finset.prod_congr rfl
    intro g hg
    apply congrArg (D g)
    funext w
    rw [← restriction_splice C x y]
    have hneg : g∉C.T := Finset.mem_compl.mp hg
    have ht : pinGroup P i w.val∉C.T := w.property.symm ▸ hneg
    simp [leftSide,ht]


abbrev LayoutReady (F : Finset (W×W)) (reg : ∀ v, GraphCutMoments.degree F v=3) (f : ℤ[X]) :=
  Ready (printedParams (f:=f) (ell:=1) (oldRowSize F)) (sourceDelta (oldRowSize F))
    (oldRowRoot F reg f (fun _=>false))

#print axioms restriction_splice
#print axioms true_D_cut
end
end V8NativeMessage.N4