import V8NativeMessageC3NativeAssemblyN2MainRun
import MainClonedCNF
import Mathlib.RingTheory.AdjoinRoot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

/-! Literal four-copy variables, unary pins, edge ORs, and implication
cycle factors. The public replacement polynomials and source measurement
layout at the fixed address are data; the fold is not given an A_g oracle. -/
namespace V8NativeMessage.C3.NativeAssembly.MainScan
open scoped Classical Polynomial BigOperators
open Polynomial
noncomputable section

abbrev Clone (W : Type*) := W × Fin 4
abbrev Clause {W : Type*} (F : Finset (W × W)) := W ⊕ (F ⊕ Clone W)
abbrev Jet (J : ℕ) := AdjoinRoot ((X:ℚ[X])^J)

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W × W)} {r Q J : ℕ}

structure CloneTuple (F : Finset (W × W)) (r Q J : ℕ) where
  frame : Frame (Clone W) (Fin r)
  node : Fin Q
  U : Finset (Clone W)
  correction_subset : U⊆frame.E
  correction_order : frame.E.card≤J-1
  factorGroup : Clause F→Fin r
  replacement : Clause F→Clone W→Clone W→ℚ[X]

def nodeValue (L : CloneTuple F r Q J) : ℚ := (L.node.val:ℚ)+1

/-- MAIN's source substitution P(t)·x^rep+(P(t+z)−P(t))·1_U. -/
def θ (L : CloneTuple F r Q J) (x : Clone W→Bool) (f : Clause F) (j : Clone W) : Jet J :=
  AdjoinRoot.mk _ (C (∑ v : Clone W, (L.replacement f j v).eval (nodeValue L) *
      (if x v then 1 else 0)) +
    ∑ v ∈ L.U, ((L.replacement f j v).comp (C (nodeValue L)+X) -
      C ((L.replacement f j v).eval (nodeValue L))))

def signedLiteral (x : Jet J) (s : Bool) : Jet J := if s then x else 1-x

def cloneFactor (F : Finset (W×W)) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (L : CloneTuple F r Q J) (s : W→Bool) (x : Clone W→Bool) :
    Clause F→Jet J
  | .inl v => signedLiteral (θ L x (.inl v) (v,0)) (s v)
  | .inr (.inl e) =>
    1-(1-θ L x (.inr (.inl e)) (e.val.1,MainClonedCNF.leftSlot F hreg e))*
      (1-θ L x (.inr (.inl e)) (e.val.2,MainClonedCNF.rightSlot F hreg e))
  | .inr (.inr (v,j)) =>
    1-θ L x (.inr (.inr (v,j))) (v,j)*(1-θ L x (.inr (.inr (v,j))) (v,j+1))

def nativeGroup (F : Finset (W×W)) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (L : CloneTuple F r Q J) (s : W→Bool) (g : Fin r) (x : Clone W→Bool) : Jet J :=
  ∏ c ∈ (Finset.univ : Finset (Clause F)).filter (fun c => L.factorGroup c=g), cloneFactor F hreg L s x c

def nativeScan (F : Finset (W×W)) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (L : CloneTuple F r Q J) (s : W→Bool) : Meter (Jet J) :=
  acceptedRun L.frame (nativeGroup F hreg L s)

theorem real_signed_unary_factor (F : Finset (W×W)) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (L : CloneTuple F r Q J) (s : W→Bool) (x : Clone W→Bool) (v : W) :
    cloneFactor F hreg L s x (.inl v)=signedLiteral (θ L x (.inl v) (v,0)) (s v) := rfl

theorem native_value_uses_representatives (F : Finset (W×W)) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (L : CloneTuple F r Q J) (s : W→Bool) (h : feasible L.frame) :
    (nativeScan F hreg L s).2.2 =
      ∏ g : Fin r, ∑ x ∈ (Finset.univ : Finset (Word L.frame g)).filter (eligible L.frame g),
        nativeGroup F hreg L s g (merge L.frame (repWord L.frame h) g x) := by
  rw [nativeScan,accepted_tuple_value L.frame (nativeGroup F hreg L s) h]
  apply Finset.prod_congr rfl
  intro g _
  exact Finset.sum_congr (by ext x; simp) (fun _ _ => rfl)

/-- An exact form of 2^(4N/r) second-pass word tests on the true four-copy
size. Applies even when the accumulated jet or a whole group's allowed
contribution is zero. -/
theorem native_four_copy_N2 (F : Finset (W×W)) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (L : CloneTuple F r Q J) (s : W→Bool) (h : feasible L.frame) (hr : 0<r) :
    (2:ℕ)^(4*Fintype.card W)≤((nativeScan F hreg L s).1)^r := by
  letI : Nonempty (Fin r) := ⟨⟨0,hr⟩⟩
  have hh := accepted_run_exponent L.frame (nativeGroup F hreg L s) h
  simpa only [Clone,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm (Fintype.card W) 4] using hh

#print axioms real_signed_unary_factor
#print axioms native_value_uses_representatives
#print axioms native_four_copy_N2
end
end V8NativeMessage.C3.NativeAssembly.MainScan
