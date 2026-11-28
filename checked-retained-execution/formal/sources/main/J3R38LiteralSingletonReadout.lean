import J3R38LiteralSingletonValue

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6500000

/-! The original MAIN first derivative test at one true register address.
The constant and first coefficient are both read from the same native
truncated result; public coefficients use the same replacement family. -/
namespace J3R38LiteralSingleton
open Polynomial V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N1
open V8NativeMessage.N6.MainFiber
open scoped Polynomial BigOperators Classical

noncomputable section

variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J R : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

def rowConstant (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (Prow : Replacement F) (t : Fin Q) (o : Occ F) : ℚ :=
  ∑ x : Clone W, (Prow (occClause o) (occVar hreg o) x).eval ((t.val:ℚ)+1)

def rowDerivative (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (Prow : Replacement F) (a : Address W Q) (o : Occ F) : ℚ :=
  (Prow (occClause o) (occVar hreg o) a.2).derivative.eval ((a.1.val:ℚ)+1)

def pinConstant (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (Prow : Replacement F) (t : Fin Q) (v : W) : ℚ :=
  rowConstant hreg Prow t (.inl v)

def pinDerivative (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (Prow : Replacement F) (a : Address W Q) (v : W) : ℚ :=
  rowDerivative hreg Prow a (.inl v)

def backgroundConstant (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (Prow : Replacement F) (t : Fin Q) : ℚ :=
  ∏ f : F ⊕ Clone W, match f with
  | .inl e => 1-(1-rowConstant hreg Prow t (.inr (.inl (e,true))))*
      (1-rowConstant hreg Prow t (.inr (.inl (e,false))))
  | .inr i => 1-rowConstant hreg Prow t (.inr (.inr (i,true)))*
      (1-rowConstant hreg Prow t (.inr (.inr (i,false))))

/-- Exactly the original graph test, independently of the direction. -/
def Admissible (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (Prow : Replacement F) (t : Fin Q) : Prop :=
  backgroundConstant hreg Prow t ≠ 0 ∧
    (∀ v, pinConstant hreg Prow t v ≠ 0) ∧ (∀ v, pinConstant hreg Prow t v ≠ 1)

theorem rowAtOne_coeff_zero (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (L : CloneTuple F r Q J) (o : Occ F) :
    (rowAtOne L hreg o).coeff 0 = rowConstant hreg L.replacement L.node o := by
  simp only [rowAtOne,thetaPoly,rowConstant,row,nodeValue,if_true,mul_one,coeff_add,
    coeff_C_zero,finset_sum_coeff,coeff_sub,comp_affine_coeff_zero,sub_self,
    Finset.sum_const_zero,add_zero]

theorem rowAtOne_coeff_one (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (L : CloneTuple F r Q J) (i : Clone W) (hi : L.U={i}) (o : Occ F) :
    (rowAtOne L hreg o).coeff 1 = rowDerivative hreg L.replacement (L.node,i) o := by
  simp only [rowAtOne,thetaPoly,hi,Finset.sum_singleton,coeff_add,coeff_sub,
    comp_affine_coeff_one]
  simp [rowDerivative,row,nodeValue]

theorem public_constant_is_Bt (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (L : CloneTuple F r Q J) :
    (backgroundPoly L hreg).coeff 0 = backgroundConstant hreg L.replacement L.node := by
  rw [backgroundPoly,coeff_zero_prod,backgroundConstant]
  apply Finset.prod_congr rfl
  intro f _
  cases f <;> simp [publicFactor,coeff_sub,mul_coeff_zero,rowAtOne_coeff_zero]

def rawJet (P : Seating F Copy r Q hreg) (R : ℕ) (hJ : 2≤J)
    (Prow : Replacement F) (a : Address W Q) (s : W→Bool) : Jet J :=
  (nativeScan F hreg (literalTuple P R hJ Prow a) s).2.2

def graphEntry (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (Prow : Replacement F) (a : Address W Q) (v : W) : ℚ :=
  pinDerivative hreg Prow a v /
    (pinConstant hreg Prow a.1 v * (1-pinConstant hreg Prow a.1 v))

/-- (h_ti/H_t - b_ti/B_t) plus the public normalization in original J3. -/
def normalize (P : Seating F Copy r Q hreg) (R : ℕ) (hJ : 2≤J)
    (Prow : Replacement F) (a : Address W Q) (received : Jet J) : ℚ :=
  jetCoeff 1 received / jetCoeff 0 received -
    (backgroundPoly (literalTuple P R hJ Prow a) hreg).coeff 1 /
      backgroundConstant hreg Prow a.1 +
    ∑ v, pinDerivative hreg Prow a v / (1-pinConstant hreg Prow a.1 v)

theorem original_J3_equation (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2≤J) (hr : 2≤r) (hR : 1≤R) (hfit : 6*R≤Q)
    (a : Address W Q) (ok : Admissible hreg Prow a.1) (s : W→Bool) :
    jetCoeff 0 (rawJet P R hJ Prow a s) ≠ 0 ∧
    normalize P R hJ Prow a (rawJet P R hJ Prow a s) =
      ∑ v, graphEntry hreg Prow a v * JointContraction.bitScalar ℚ (s v) := by
  let L := literalTuple P R hJ Prow a
  let p := fun v : W => rowAtOne L hreg (.inl v)
  let B := backgroundPoly L hreg
  have h0 (v : W) : (p v).coeff 0 = pinConstant hreg Prow a.1 v :=
    rowAtOne_coeff_zero hreg L (.inl v)
  have h1 (v : W) : (p v).coeff 1 = pinDerivative hreg Prow a v :=
    rowAtOne_coeff_one hreg L a.2 rfl (.inl v)
  have hb : B.coeff 0 = backgroundConstant hreg Prow a.1 := public_constant_is_Bt hreg L
  have hx : rawJet P R hJ Prow a s = AdjoinRoot.mk _ (B * ∏ v,
      JointContraction.pinPolynomial (s v) (p v)) :=
    true_jet_from_one_point P Prow hJ hr hR hfit a s
  have hb₀ : B.coeff 0 ≠ 0 := by rw [hb]; exact ok.1
  have hp₀ (v : W) : (p v).coeff 0 ≠ 0 := by rw [h0]; exact ok.2.1 v
  have hp₁ (v : W) : (p v).coeff 0 ≠ 1 := by rw [h0]; exact ok.2.2 v
  have hz := joint_constant_ne_zero B p s hb₀ hp₀ hp₁
  have hg := JointContraction.singleton_pin_first B p s hb₀ hp₀ hp₁
  rw [hx]
  constructor
  · rw [jetCoeff_mk (show 0<J by omega)]
    exact hz
  · unfold normalize graphEntry
    rw [jetCoeff_mk (show 1<J by omega),jetCoeff_mk (show 0<J by omega)]
    dsimp only at hg
    simp_rw [h0,h1,hb] at hg
    exact hg

/-- H_t is the zeroth coefficient read on any requested direction at the
same node. Its right-hand side has no dependence on that direction. -/
theorem actual_constant_is_Ht (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2≤J) (hr : 2≤r) (hR : 1≤R) (hfit : 6*R≤Q)
    (a : Address W Q) (s : W→Bool) :
    jetCoeff 0 (rawJet P R hJ Prow a s) =
      backgroundConstant hreg Prow a.1 *
        ∏ v : W,(if s v then pinConstant hreg Prow a.1 v else 1-pinConstant hreg Prow a.1 v) := by
  unfold rawJet
  rw [true_jet_from_one_point P Prow hJ hr hR hfit a s,jetCoeff_mk (show 0<J by omega),
    onePointProduct,mul_coeff_zero,coeff_zero_prod,public_constant_is_Bt]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  cases s v <;> simp [JointContraction.pinPolynomial,rowAtOne_coeff_zero,
    pinConstant,literalTuple]

#print axioms actual_constant_is_Ht
#print axioms rowAtOne_coeff_zero
#print axioms rowAtOne_coeff_one
#print axioms public_constant_is_Bt
#print axioms original_J3_equation

end
end J3R38LiteralSingleton
