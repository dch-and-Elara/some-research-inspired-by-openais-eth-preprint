import V8NativeMessageN3LiteralRank

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-! Explicit coefficient readouts through order j on the original four
copy jet. The lower-order width comes from a proved quotient identity,
not a dimension or low-rank assumption. -/
namespace V8NativeMessage.N3Literal
open scoped Classical BigOperators Polynomial
open Polynomial V8NativeMessage.C3.NativeAssembly.MainScan
open Paper5.HybridClosure
noncomputable section

/-- The actual coefficient of the canonical jet representative. -/
def coefficient (d j : ℕ) : Jet d→ₗ[ℚ]ℚ :=
  (Polynomial.lcoeff ℚ j).comp
    (AdjoinRoot.modByMonicHom ((monic_X : Monic (X : ℚ[X])).pow d))

theorem mod_X_pow_coeff (p : ℚ[X]) {d j : ℕ} (hj : j<d) :
    (p %ₘ (X:ℚ[X])^d).coeff j=p.coeff j := by
  rw [modByMonic_eq_sub_mul_div p (monic_X.pow d),coeff_sub,coeff_X_pow_mul',if_neg hj.not_ge,sub_zero]

theorem coefficient_after_shrink {k J j : ℕ} (fit : k≤J) (hj : j<k) (x : Jet J) :
    coefficient k j (N4.shrink fit x)=coefficient J j x := by
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective x
  have h : N4.shrink fit (AdjoinRoot.mk ((X:ℚ[X])^J) p)=AdjoinRoot.mk ((X:ℚ[X])^k) p := by
    rw [N4.shrink,AdjoinRoot.algHomOfDvd,AdjoinRoot.liftHom_mk,AdjoinRoot.aeval_eq]
  rw [h]
  simp only [coefficient,LinearMap.comp_apply,AdjoinRoot.modByMonicHom_mk,Polynomial.lcoeff_apply]
  exact (mod_X_pow_coeff p hj).trans (mod_X_pow_coeff p (hj.trans_le fit)).symm

/-- A fixed rational linear combination of coefficients numbered below k. -/
def lowReadout (d k : ℕ) (weights : Fin k→ℚ) : Jet d→ₗ[ℚ]ℚ :=
  ∑ j : Fin k, weights j • coefficient d j.val

theorem lowReadout_shrink {k J : ℕ} (fit : k≤J) (weights : Fin k→ℚ) (x : Jet J) :
    lowReadout k k weights (N4.shrink fit x)=lowReadout J k weights x := by
  simp only [lowReadout,LinearMap.sum_apply,LinearMap.smul_apply]
  exact Finset.sum_congr rfl (fun j _ => congrArg (weights j • ·) (coefficient_after_shrink fit j.isLt x))

/-- Use the canonical polynomial to embed the lower jet linearly. This
lifting does not assert preservation of products. -/
def liftPrefix (k J : ℕ) : Jet k→ₗ[ℚ]Jet J :=
  (AdjoinRoot.mkₐ ((X:ℚ[X])^J)).toLinearMap.comp
    (AdjoinRoot.modByMonicHom ((monic_X : Monic (X : ℚ[X])).pow k))

theorem coefficient_liftPrefix {k J j : ℕ} (hj : j<J) (x : Jet k) :
    coefficient J j (liftPrefix k J x)=coefficient k j x := by
  change ((AdjoinRoot.modByMonicHom ((monic_X : Monic (X : ℚ[X])).pow k) x) %ₘ
    (X:ℚ[X])^J).coeff j = _
  exact mod_X_pow_coeff _ hj

/-- Dependence on these actual low coefficients suffices; the readout
need not be supplied already written as a linear form on the quotient. -/
theorem readout_factors_of_low_dependency {k J : ℕ} (fit : k≤J) (read : Jet J→ₗ[ℚ]ℚ)
    (onlyLow : ∀ x y : Jet J,
      (∀ j : Fin k, coefficient J j.val x=coefficient J j.val y) → read x=read y) :
    ∃ ρ : Jet k→ₗ[ℚ]ℚ, ∀ x, read x=ρ (N4.shrink fit x) := by
  refine ⟨read.comp (liftPrefix k J),?_⟩
  intro x
  change read x=read (liftPrefix k J (N4.shrink fit x))
  apply onlyLow
  intro j
  exact (coefficient_after_shrink fit j.isLt x).symm.trans
    (coefficient_liftPrefix (j.isLt.trans_le fit) (N4.shrink fit x)).symm

section Source
variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)} {r Q J : ℕ}
variable (L : CloneTuple F r Q J) (reg : ∀v,GraphCutMoments.degree F v=3)
variable (h : feasible L.frame) (cut : W→Bool)

/-- The exact original order-j formulation for arbitrary fixed lists. -/
theorem original_N3_through_order (P : N6.FixedLists L) (j : ℕ) (fit : j+1≤J)
    (weights : Fin (j+1)→ℚ) :
    (Matrix.of (fun (x : RowWord cut) (y : ColWord cut) =>
      lowReadout J (j+1) weights (N6.completed L reg h P (signs cut x y)))).rank≤
        (j+1)*∏ g, P.count g := by
  have e : (Matrix.of (fun (x : RowWord cut) (y : ColWord cut) =>
      lowReadout J (j+1) weights (N6.completed L reg h P (signs cut x y)))) =
        sourceMatrix L reg h P fit (lowReadout (j+1) (j+1) weights) cut := by
    ext x y
    simp only [Matrix.of_apply,sourceMatrix,lowReadout_shrink]
  rw [e]
  exact original_N3_fixed_prefix L reg h P fit _ cut
/-- The same sharp order parameter for any fixed linear functional
which is determined by the actual retained coefficients. -/
theorem original_N3_low_dependency (P : N6.FixedLists L) {k : ℕ} (fit : k≤J)
    (read : Jet J→ₗ[ℚ]ℚ)
    (onlyLow : ∀ x y : Jet J,
      (∀ j : Fin k, coefficient J j.val x=coefficient J j.val y) → read x=read y) :
    (Matrix.of (fun (x : RowWord cut) (y : ColWord cut) =>
      read (N6.completed L reg h P (signs cut x y)))).rank≤k*∏ g,P.count g := by
  obtain ⟨ρ,eρ⟩ := readout_factors_of_low_dependency fit read onlyLow
  have e : (Matrix.of (fun (x : RowWord cut) (y : ColWord cut) =>
      read (N6.completed L reg h P (signs cut x y)))) = sourceMatrix L reg h P fit ρ cut := by
    ext x y
    exact eρ _
  rw [e]
  exact original_N3_fixed_prefix L reg h P fit ρ cut
end Source

section TriangleReplacement
variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (cubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E) {r Q J : ℕ}

/-- The printed scanner on the original triangle-replaced cubic graph;
its factor tables are the four-clone literal unary, OR and implication
clauses, not an abstract or five-copy substitute. -/
theorem original_N3_triangle_replacement_scan
    (L : CloneTuple (replacedEdges E cubic) r Q J) (h : feasible L.frame)
    (cut : TriVertex V→Bool) (j : ℕ) (fit : j+1≤J) (weights : Fin (j+1)→ℚ) :
    (Matrix.of (fun (x : RowWord cut) (y : ColWord cut) =>
      lowReadout J (j+1) weights ((nativeScan (replacedEdges E cubic)
        (replaced_cubic E cubic loopless) L (signs cut x y)).2.2))).rank≤
        (j+1)*∏ g, Fintype.card (N6.PrivateWord L g) := by
  have e : (Matrix.of (fun (x : RowWord cut) (y : ColWord cut) =>
      lowReadout J (j+1) weights ((nativeScan (replacedEdges E cubic)
        (replaced_cubic E cubic loopless) L (signs cut x y)).2.2))) =
      sourceMatrix L (replaced_cubic E cubic loopless) h (N6.exhaustive L) fit
        (lowReadout (j+1) (j+1) weights) cut := by
    ext x y
    simp only [Matrix.of_apply,sourceMatrix,N6.exhaustive_completed L (replaced_cubic E cubic loopless) h,
      lowReadout_shrink]
  rw [e]
  exact original_N3_fixed_prefix L (replaced_cubic E cubic loopless) h (N6.exhaustive L) fit _ cut
end TriangleReplacement

#print axioms mod_X_pow_coeff
#print axioms coefficient_after_shrink
#print axioms lowReadout_shrink
#print axioms coefficient_liftPrefix
#print axioms readout_factors_of_low_dependency
#print axioms original_N3_through_order
#print axioms original_N3_low_dependency
#print axioms original_N3_triangle_replacement_scan
end
end V8NativeMessage.N3Literal
