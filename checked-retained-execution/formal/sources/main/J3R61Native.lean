import J3R61Product

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5200000

/-! Specialize the executed integer program to the actual J3 address.
The signed forward sampler and the graph-only public score are distinct
interfaces. Neither pretends to acquire an unknown oracle value. -/
namespace J3R61
open Polynomial V8NativeMessage J3R60
open V8NativeMessage.C3.NativeAssembly.MainScan V8NativeMessage.N6.MainFiber
open J3R38LiteralSingleton
open scoped BigOperators Polynomial Classical
noncomputable section

variable {W Copy : Type*} [Fintype W] [DecidableEq W] [Fintype Copy]
variable {F : Finset (W×W)} {r Q J R BP : ℕ}
variable {hreg : ∀ v, GraphCutMoments.degree F v=3}

def runNative (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (R : ℕ) (a : Address W Q) (s : W → Bool) : Paid (Pair ℚ) :=
  signedRun (literalTuple P R hJ Prow a) hreg R a.2 s Finset.univ

theorem runNative_same_first_jet (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (hr : 2 ≤ r) (hR : 1 ≤ R) (hfit : 6*R ≤ Q)
    (a : Address W Q)
    (hb : N1.RowBound (literalTuple P R hJ Prow a) hreg R BP) (s : W → Bool) :
    (runNative P Prow hJ R a s).value = jetTwo (rawJet P R hJ Prow a s) := by
  unfold runNative
  let L := literalTuple P R hJ Prow a
  rw [signedRun_exact L hb hJ a.2 rfl s Finset.univ,←mk_onePointProduct L hreg s]
  exact congrArg jetTwo (true_jet_from_one_point P Prow hJ hr hR hfit a s).symm

theorem runNative_source_visits (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (R : ℕ) (a : Address W Q) (s : W → Bool) :
    (runNative P Prow hJ R a s).ops ≤
      (R-1)+Q+1+3+(rowOps R (4*Fintype.card W)+10)*(12*Fintype.card W) := by
  have hh := signedRun_ops (literalTuple P R hJ Prow a) hreg (R:=R) a.2 s Finset.univ
  rw [degreeOn,N1.native_degree hreg] at hh
  exact hh

def publicSet (F : Finset (W×W)) : Finset (Clause F) :=
  (Finset.univ : Finset (F ⊕ Clone W)).map ⟨Sum.inr,Sum.inr_injective⟩

def runPublic (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (R : ℕ) (i : Clone W) : Paid (Pair ℚ) :=
  signedRun L hreg R i (fun _=>false) (publicSet F)

theorem runPublic_exact (L : CloneTuple F r Q J) (bounds : N1.RowBound L hreg R BP)
    (hJ : 2 ≤ J) (i : Clone W) (hi : L.U={i}) :
    (runPublic L hreg R i).value = capture (backgroundPoly L hreg) := by
  unfold runPublic
  rw [signedRun_exact L bounds hJ i hi, publicSet,Finset.prod_map]
  have he : (∏ f : F ⊕ Clone W, cloneFactor F hreg L (fun _=>false) (fun _=>true)
      (Sum.inr f)) = AdjoinRoot.mk ((X:ℚ[X])^J) (backgroundPoly L hreg) := by
    simp only [backgroundPoly,map_prod]
    apply Finset.prod_congr rfl
    intro f _
    rcases f with (e|i) <;>
      simp [publicFactor,rowAtOne,N1.thetaPoly_mk,cloneFactor,N1.occClause,N1.occVar]
  change jetTwo (∏ f : F ⊕ Clone W, cloneFactor F hreg L (fun _=>false) (fun _=>true)
    (Sum.inr f)) = _
  rw [he]
  exact Pair.ext' (jetCoeff_mk (show 0<J by omega) _) (jetCoeff_mk (show 1<J by omega) _)

theorem runPublic_ops (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (R : ℕ) (i : Clone W) :
    (runPublic L hreg R i).ops ≤
      (R-1)+Q+1+3+(rowOps R (4*Fintype.card W)+10)*(12*Fintype.card W) := by
  have hh := signedRun_ops L hreg (R:=R) i (fun _=>false) (publicSet F)
  apply hh.trans
  have hd : degreeOn (publicSet F) ≤ 12*Fintype.card W := by
    rw [←N1.native_degree hreg]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hd) _

def runPin (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (R : ℕ) (i : Clone W) (v : W) : Paid (Pair ℚ) :=
  let D := printedScale R Q
  let p := literalRead L hreg D.value R i (.inl v)
  ⟨rationalPair p.value D.value,D.ops+1+p.ops+2⟩

theorem runPin_exact (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (a : Address W Q)
    (hb : N1.RowBound (literalTuple P R hJ Prow a) hreg R BP) (v : W) :
    (runPin (literalTuple P R hJ Prow a) hreg R a.2 v).value =
      ⟨pinConstant hreg Prow a.1 v,pinDerivative hreg Prow a v⟩ := by
  let L := literalTuple P R hJ Prow a
  change rationalPair (literalRead L hreg (printedScale R Q).value R a.2 (.inl v)).value
    (printedScale R Q).value = _
  rw [literalRead_at_printed L hreg R a.2 (.inl v), literalRow_same_itheta L hb a.2 rfl,
    (printedScale_exact R Q).1]
  have h := N1.jetify_iTheta L hreg hb (fun _=>true) (.inl v)
  rw [← N1.thetaPoly_mk L hreg (fun _=>true) (.inl v)] at h
  rw [captured_scaled_jet hJ _ (N1.δ_pos R Q) _ _ h]
  apply Pair.ext'
  · exact (jetCoeff_mk (show 0<J by omega) _).trans (rowAtOne_coeff_zero hreg L (.inl v))
  · exact (jetCoeff_mk (show 1<J by omega) _).trans (rowAtOne_coeff_one hreg L a.2 rfl (.inl v))

theorem runPin_ops (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (R : ℕ) (i : Clone W) (v : W) :
    (runPin L hreg R i v).ops = (R-1)+Q+1+3+rowOps R (4*Fintype.card W) := by
  simp only [runPin,literalRead_at_printed,literalRow_ops,(printedScale_exact R Q).2]
  omega

def runGraph (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (R : ℕ) (i : Clone W) (v : W) : Paid ℚ :=
  let pin := runPin L hreg R i v
  ⟨pin.value.d/(pin.value.c*(1-pin.value.c)),pin.ops+3⟩

theorem runGraph_original (P : Seating F Copy r Q hreg) (Prow : Replacement F)
    (hJ : 2 ≤ J) (a : Address W Q)
    (hb : N1.RowBound (literalTuple P R hJ Prow a) hreg R BP) (v : W) :
    (runGraph (literalTuple P R hJ Prow a) hreg R a.2 v).value = graphEntry hreg Prow a v := by
  simp only [runGraph,runPin_exact P Prow hJ a hb,graphEntry]

theorem runGraph_arithmetic (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
    (R : ℕ) (i : Clone W) (v : W) :
    (runGraph L hreg R i v).ops=(R-1)+Q+1+6+rowOps R (4*Fintype.card W) := by
  simp only [runGraph,runPin_ops]
  omega

#print axioms runNative_same_first_jet
#print axioms runNative_source_visits
#print axioms runPublic_exact
#print axioms runPublic_ops
#print axioms runPin_exact
#print axioms runPin_ops
#print axioms runGraph_original
#print axioms runGraph_arithmetic

end
end J3R61
