import J3R38LiteralSingletonReadout
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5900000

/-! Assemble the literal, graph-testable J3 decoder.  A full-column-rank
condition on the actual displayed matrix is the only reconstruction
condition; neither good readout values nor an inverse is supplied. -/
namespace J3R38LiteralSingleton
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber
open scoped BigOperators Classical

noncomputable section

variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J R : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

def graphMatrix (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (Prow : Replacement F) (A : Finset (Address W Q)) : Matrix {a // a∈A} W ℚ :=
  Matrix.of (fun a v=>graphEntry hreg Prow a.val v)

omit [DecidableEq W] in
theorem menu_size (A : Finset (Address W Q)) : A.card≤Q*(4*Fintype.card W) := by
  have hc := A.card_le_univ
  simpa only [Address,Clone,Fintype.card_prod,Fintype.card_fin,Nat.mul_comm (Fintype.card W) 4] using hc

theorem original_J3 (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2≤J) (hr : 2≤r) (hR : 1≤R) (hfit : 6*R≤Q)
    (A : Finset (Address W Q)) (ok : ∀ a ∈ A, Admissible hreg Prow a.1)
    (hRank : (graphMatrix hreg Prow A).rank=Fintype.card W) :
    A.card≤Q*(4*Fintype.card W) ∧
      (∀ (a : {a // a∈A}) s, jetCoeff 0 (rawJet P R hJ Prow a.val s) ≠ 0) ∧
      ∃ decode : ({a // a∈A}→Jet J)→W→Bool,
        ∀ s : W→Bool, decode (fun a=>rawJet P R hJ Prow a.val s)=s := by
  let M := graphMatrix hreg Prow A
  have hdim : M.rank + Module.finrank ℚ (LinearMap.ker M.mulVecLin) = Fintype.card W := by
    simpa only [Matrix.rank,Module.finrank_pi] using
      (LinearMap.finrank_range_add_finrank_ker M.mulVecLin)
  have hM : M.rank=Fintype.card W := hRank
  have hk : LinearMap.ker M.mulVecLin=⊥ := by
    apply Submodule.finrank_eq_zero.mp
    omega
  obtain ⟨inverse,left⟩ := LinearMap.exists_leftInverse_of_injective M.mulVecLin hk
  refine ⟨menu_size A,fun a s=>(original_J3_equation P Prow hJ hr hR hfit a.val
    (ok _ a.property) s).1,?_⟩
  refine ⟨fun received v=>decide ((inverse (fun a=>normalize P R hJ Prow a.val (received a))) v=1),?_⟩
  intro s
  let bits := fun v : W => JointContraction.bitScalar ℚ (s v)
  have obs : (fun a : {a // a∈A}=>normalize P R hJ Prow a.val (rawJet P R hJ Prow a.val s)) =
      M.mulVecLin bits := by
    funext a
    exact (original_J3_equation P Prow hJ hr hR hfit a.val (ok _ a.property) s).2
  have lift := LinearMap.congr_fun left bits
  change inverse (M.mulVecLin bits)=bits at lift
  funext v
  change decide ((inverse (fun a : {a // a∈A}=>normalize P R hJ Prow a.val
    (rawJet P R hJ Prow a.val s))) v=1)=s v
  rw [obs,lift]
  cases hs : s v <;> simp [bits,JointContraction.bitScalar,hs]

#print axioms menu_size
#print axioms original_J3

end
end J3R38LiteralSingleton
