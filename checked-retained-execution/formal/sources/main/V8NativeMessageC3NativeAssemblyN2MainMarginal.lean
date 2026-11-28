import V8NativeMessageC3NativeAssemblyN2MainClone
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

/-! The individually requested MAIN group recovers the manuscript's
finite lower exponent from the full variable marginal certificate,
not merely from an upper group-size bound. -/
namespace V8NativeMessage.C3.NativeAssembly.MainScan
open scoped Classical BigOperators
noncomputable section

variable {V I G : Type*} [Fintype V] [Fintype I] [Fintype G]

def sizeAt (L : I→V→G) (t : I) (g : G) : ℕ := Fintype.card {v : V // L t v=g}

def meanSize (V G : Type*) [Fintype V] [Fintype G] : ℝ :=
  (Fintype.card V:ℝ)/Fintype.card G

def xi (L : I→V→G) : ℝ :=
  ∑ t : I, ∑ g : G, ((sizeAt L t g:ℝ)-meanSize V G)^2

theorem one_marginal_square_le_xi (L : I→V→G) (t : I) (g : G) :
    ((sizeAt L t g:ℝ)-meanSize V G)^2≤xi L := by
  have harg : ((sizeAt L t g:ℝ)-meanSize V G)^2 ≤
      ∑ k : G, ((sizeAt L t k:ℝ)-meanSize V G)^2 :=
    Finset.single_le_sum (f:=fun k : G => ((sizeAt L t k:ℝ)-meanSize V G)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ g)
  exact harg.trans (Finset.single_le_sum
    (f:=fun c : I => ∑ k : G, ((sizeAt L c k:ℝ)-meanSize V G)^2)
    (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ t))

theorem main_marginal_lower (L : I→V→G)
    (h : xi L≤2*(Fintype.card I:ℝ)*Fintype.card V) (t : I) (g : G) :
    meanSize V G-Real.sqrt (2*(Fintype.card I:ℝ)*Fintype.card V)≤sizeAt L t g := by
  let B : ℝ := 2*(Fintype.card I:ℝ)*Fintype.card V
  let d : ℝ := meanSize V G-(sizeAt L t g:ℝ)
  let c : ℝ := Real.sqrt B
  have hB : 0≤B := by dsimp [B]; positivity
  have hc : 0≤c := Real.sqrt_nonneg _
  have hcc : c^2=B := Real.sq_sqrt hB
  have hd : d^2≤B := by
    have h2 := (one_marginal_square_le_xi L t g).trans h
    dsimp [d,B]
    nlinarith
  change meanSize V G-c≤sizeAt L t g
  by_contra! hx
  have hcd : c<d := by dsimp [d]; linarith
  have hdc : 0<d+c := by linarith
  nlinarith [mul_pos (sub_pos.mpr hcd) hdc]

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J : ℕ}

theorem individual_source_group_N2 (F : Finset (W×W))
    (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (L : Fin Q→CloneTuple F r Q J) (s : W→Bool)
    (hXi : xi (fun t => (L t).frame.group) ≤ 2*(Fintype.card (Fin Q):ℝ)*Fintype.card (Clone W))
    (t : Fin Q) (g : Fin r) (hf : feasible (L t).frame) :
    (secondScan (L t).frame (nativeGroup F hreg (L t) s) hf g).1 =
      2^sizeAt (fun u => (L u).frame.group) t g ∧
    meanSize (Clone W) (Fin r) - Real.sqrt (2*(Fintype.card (Fin Q):ℝ)*Fintype.card (Clone W)) ≤
      sizeAt (fun u => (L u).frame.group) t g :=
  ⟨second_tests_every_word _ _ _ _, main_marginal_lower (fun u => (L u).frame.group) hXi t g⟩

#print axioms one_marginal_square_le_xi
#print axioms main_marginal_lower
#print axioms individual_source_group_N2
end
end V8NativeMessage.C3.NativeAssembly.MainScan
