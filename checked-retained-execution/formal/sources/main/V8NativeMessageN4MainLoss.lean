import V8NativeMessageN1MainHeight
import V8NativeMessageN6MainLocal
import V8NativeMessageC3HermiteNative

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4800000

/-! MAIN part of the actual N4 ordinary denominator ledger, for the
original four-copy degree 12N, not the five-copy degree in C3. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6R9Recursive
open V8NativeMessage.C3.RawMain V8NativeMessage.C3.Hermite V8NativeMessage.C3.Canonical
open V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W] {F : Finset (W×W)} {r Q J R BP : ℕ}
variable (L : CloneTuple F r Q J) (reg : ∀ v, GraphCutMoments.degree F v=3)
  (H : N1.RowBound L reg R BP) (ok : feasible L.frame) (points : N6.FixedLists L)

include H in
theorem true_group_scaled_jet (g : Fin r) (x : Clone W→Bool) (σ : W→Bool) :
    ((N1.δ R Q:Jet J)^(N1.groupDeg L g)*nativeGroup F reg L σ g x)∈localJetImage J := by
  have hh : N1.jetify J (N1.intGroup L reg H σ g x)∈localJetImage J :=
    integer_to_local_jet J ⟨N1.intGroup L reg H σ g x,rfl⟩
  exact (N1.int_group_lift L reg H σ g x) ▸ hh

include H in
theorem fixed_groups_scaled_jet (hw : ∀ g j, points.weight g j∈localJetImage J)
    (σ : W→Bool) :
    ((N1.δ R Q:Jet J)^(12*Fintype.card W)*N6.completed L reg ok points σ)∈localJetImage J := by
  let a : Jet J := N1.δ R Q
  have hd : (∑ g, N1.groupDeg L g)=12*Fintype.card W := by
    rw [N1.total_group_degree L,N1.native_degree reg]
  have he : (∏ g, a^(N1.groupDeg L g)*N6.groupJet L reg ok points g σ) =
      a^(12*Fintype.card W)*N6.completed L reg ok points σ := by
    rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hd]
    rfl
  change a^(12*Fintype.card W)*N6.completed L reg ok points σ∈localJetImage J
  rw [←he]
  apply Subring.prod_mem
  intro g _
  rw [N6.groupJet,Finset.mul_sum]
  apply Subring.sum_mem
  intro k _
  unfold N6.entry
  rw [show a^(N1.groupDeg L g)*(points.weight g k*nativeGroup F reg L σ g (N6.fullPoint L ok points g k))=
      points.weight g k*(a^(N1.groupDeg L g)*nativeGroup F reg L σ g (N6.fullPoint L ok points g k))
    by ring]
  exact (localJetImage J).mul_mem (hw g k)
    (true_group_scaled_jet L reg H g (N6.fullPoint L ok points g k) σ)

def coefficientLoss (N R Q : ℕ) : ℕ := padicValInt 2 ((N1.δ R Q:ℕ):ℤ)*(12*N)

def mainOrdinaryLoss (N R Q J : ℕ) : ℕ := coefficientLoss N R Q + extraLoss Q J

include H in
theorem four_coefficient_loss (hw : ∀ g j, points.weight g j∈localJetImage J)
    (σ : W→Bool) (j : ℕ) :
    (2:ℚ)^coefficientLoss (Fintype.card W) R Q *
       N1.jetCoeff J j (N6.completed L reg ok points σ) ∈ twoLocalSubalgebra := by
  let x := N6.completed L reg ok points σ
  let d := 12*Fintype.card W
  have e := integral_coefficient J j _ (fixed_groups_scaled_jet L reg H ok points hw σ)
  change N1.jetCoeff J j ((N1.δ R Q:Jet J)^d*x)∈twoLocalSubalgebra at e
  rw [← Nat.cast_pow, N1.jetCoeff_scale, Nat.cast_pow] at e
  exact remove_odd_scale (N1.δ_pos R Q) d (N1.jetCoeff J j x) e

def fourMainOrigin (σ : W→Bool) : ℚ :=
  jetNodeLinear Q J (L.node.val+1) (N6.completed L reg ok points σ)

include H in
theorem four_main_origin_loss (hJ : 0<J) (hw : ∀ g j, points.weight g j∈localJetImage J)
    (f : ℤ[X]) (σ : W→Bool) :
    HasLoss f 1 (mainOrdinaryLoss (Fintype.card W) R Q J)
      (algebraMap ℚ (RatRing f 1) (fourMainOrigin L reg ok points σ)) := by
  let q := fourMainOrigin L reg ok points σ
  have hv : L.node.val+1∈nodes Q := Finset.mem_Icc.mpr ⟨by omega,L.node.isLt⟩
  have hp : (2:ℚ)^mainOrdinaryLoss (Fintype.card W) R Q J*q∈twoLocalSubalgebra := by
    change (2:ℚ)^(coefficientLoss (Fintype.card W) R Q+extraLoss Q J) *
      nodeReadout Q J (L.node.val+1) (AdjoinRoot.modByMonicHom (monic_X.pow J)
        (N6.completed L reg ok points σ))∈twoLocalSubalgebra
    apply node_readout_loss hv hJ
    intro k _
    exact four_coefficient_loss L reg H ok points hw σ k
  let a : TwoLocal := ⟨(2:ℚ)^mainOrdinaryLoss (Fintype.card W) R Q J*q,hp⟩
  refine ⟨localScalar f 1 a,?_⟩
  rw [embed_localScalar]
  change _ = algebraMap ℚ (RatRing f 1) ((2:ℚ)^mainOrdinaryLoss (Fintype.card W) R Q J*q)
  rw [map_mul,map_pow,map_ofNat]

#print axioms true_group_scaled_jet
#print axioms fixed_groups_scaled_jet
#print axioms four_coefficient_loss
#print axioms four_main_origin_loss
end
end V8NativeMessage.N4
