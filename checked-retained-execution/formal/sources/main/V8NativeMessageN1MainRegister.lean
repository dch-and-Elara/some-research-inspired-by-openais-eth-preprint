import V8NativeMessageN1MainFactor

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

/-! Exact integer numerator lifting for the actual accepted four-copy
MAIN tuple, and for every partial sum and partial product of that tuple.
The registered values remain the original Taylor quotient elements. -/
namespace V8NativeMessage.N1
open scoped Classical BigOperators Polynomial
open Polynomial V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J : ℕ}
variable (L : CloneTuple F r Q J) (hreg : ∀ v, GraphCutMoments.degree F v=3)
variable {R BP : ℕ} (H : RowBound L hreg R BP)

def groupDeg (g : Fin r) : ℕ := ∑ f ∈ clauseSet L g, arity f

def room (g : Fin r) : ℕ := Fintype.card {v : Clone W // L.frame.group v=g}

omit [DecidableEq W] in
theorem total_group_degree :
    (∑ g : Fin r, groupDeg L g)=∑ f : Clause F, arity f := by
  unfold groupDeg clauseSet
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

omit [DecidableEq W] in
theorem total_room : (∑ g : Fin r, room L g)=4*Fintype.card W := by
  have hp := Fintype.card_congr (Equiv.sigmaFiberEquiv L.frame.group)
  simpa only [room,Fintype.card_sigma,Clone,Fintype.card_prod,Fintype.card_fin,
    Nat.mul_comm (Fintype.card W) 4] using hp

def intGroup (s : W→Bool) (g : Fin r) (x : Clone W→Bool) : ℤ[X] :=
  ∏ f ∈ clauseSet L g, intFactor L hreg H s x f

theorem int_group_lift (s : W→Bool) (g : Fin r) (x : Clone W→Bool) :
    jetify J (intGroup L hreg H s g x)=(δ R Q:Jet J)^(groupDeg L g)*nativeGroup F hreg L s g x := by
  unfold intGroup groupDeg nativeGroup
  simp only [map_prod,jetify_factor,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,clauseSet]

theorem norm_group (s : W→Bool) (g : Fin r) (x : Clone W→Bool) :
    coeffNorm (intGroup L hreg H s g x)≤A W R Q BP^(groupDeg L g) := by
  unfold intGroup groupDeg
  apply (norm_prod _ _).trans
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod' (fun f _ => norm_factor L hreg H x s f)

def fullFibre (g : Fin r) : Finset (Word L.frame g) := Finset.univ.filter (eligible L.frame g)

def filled (h : feasible L.frame) (g : Fin r) (x : Word L.frame g) : Clone W→Bool :=
  merge L.frame (repWord L.frame h) g x

def intAccum (s : W→Bool) (h : feasible L.frame) (g : Fin r) (xs : Finset (Word L.frame g)) :
    ℤ[X] := ∑ x ∈ xs, intGroup L hreg H s g (filled L h g x)

def ratAccum (s : W→Bool) (h : feasible L.frame) (g : Fin r) (xs : Finset (Word L.frame g)) :
    Jet J := ∑ x ∈ xs, nativeGroup F hreg L s g (filled L h g x)

theorem int_accum_lift (s : W→Bool) (h : feasible L.frame) (g : Fin r)
    (xs : Finset (Word L.frame g)) :
    jetify J (intAccum L hreg H s h g xs)=(δ R Q:Jet J)^(groupDeg L g)*ratAccum L hreg s h g xs := by
  simp only [intAccum,ratAccum,map_sum,int_group_lift,Finset.mul_sum]

theorem norm_accum (s : W→Bool) (h : feasible L.frame) (g : Fin r)
    (xs : Finset (Word L.frame g)) :
    coeffNorm (intAccum L hreg H s h g xs)≤2^room L g*A W R Q BP^(groupDeg L g) := by
  unfold intAccum
  apply (norm_sum _ _).trans
  calc
    _ ≤ ∑ _x ∈ xs, A W R Q BP^(groupDeg L g) := Finset.sum_le_sum
      (fun x _ => norm_group L hreg H s g (filled L h g x))
    _ = xs.card * A W R Q BP^(groupDeg L g) := by simp
    _ ≤ _ := by
      apply Nat.mul_le_mul_right
      have hg : Fintype.card (Word L.frame g)=2^room L g := by simp [Word,room]
      exact (Finset.card_le_univ _).trans (le_of_eq hg)

def degreeAt (G : Finset (Fin r)) : ℕ := ∑ g ∈ G, groupDeg L g
def roomAt (G : Finset (Fin r)) : ℕ := ∑ g ∈ G, room L g

theorem degreeAt_le (hregular : ∀ v, GraphCutMoments.degree F v=3) (G : Finset (Fin r)) : degreeAt L G≤12*Fintype.card W := by
  rw [← native_degree hregular,← total_group_degree L]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ G)

omit [DecidableEq W] in
theorem roomAt_le (G : Finset (Fin r)) : roomAt L G≤4*Fintype.card W := by
  rw [← total_room L]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ G)

def intPartial (s : W→Bool) (h : feasible L.frame) (G : Finset (Fin r))
    (xs : ∀ g, Finset (Word L.frame g)) : ℤ[X] :=
  ∏ g ∈ G, intAccum L hreg H s h g (xs g)

def ratPartial (s : W→Bool) (h : feasible L.frame) (G : Finset (Fin r))
    (xs : ∀ g, Finset (Word L.frame g)) : Jet J :=
  ∏ g ∈ G, ratAccum L hreg s h g (xs g)

theorem int_partial_lift (s : W→Bool) (h : feasible L.frame) (G : Finset (Fin r))
    (xs : ∀ g, Finset (Word L.frame g)) :
    jetify J (intPartial L hreg H s h G xs)=(δ R Q:Jet J)^(degreeAt L G)*ratPartial L hreg s h G xs := by
  simp only [intPartial,ratPartial,degreeAt,map_prod,int_accum_lift,Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]

theorem norm_partial (s : W→Bool) (h : feasible L.frame) (G : Finset (Fin r))
    (xs : ∀ g, Finset (Word L.frame g)) :
    coeffNorm (intPartial L hreg H s h G xs)≤2^roomAt L G*A W R Q BP^(degreeAt L G) := by
  unfold intPartial degreeAt roomAt
  apply (norm_prod _ _).trans
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_le_prod' (fun g _ => norm_accum L hreg H s h g (xs g))

theorem completed_is_full_partial (s : W→Bool) (h : feasible L.frame) :
    (nativeScan F hreg L s).2.2=ratPartial L hreg s h Finset.univ (fullFibre L) :=
  native_value_uses_representatives F hreg L s h

#print axioms total_group_degree
#print axioms total_room
#print axioms int_group_lift
#print axioms norm_group
#print axioms int_accum_lift
#print axioms norm_accum
#print axioms degreeAt_le
#print axioms roomAt_le
#print axioms int_partial_lift
#print axioms norm_partial
#print axioms completed_is_full_partial
end
end V8NativeMessage.N1
