import P5MainBalanceM6Rows
import P5MainBalanceM6Walsh

/-! Pointwise transport of the real exceptional statistic into the
filled physical copy vector. We expand the sums instead of identifying
nondefinitionally equal Fintype instances on the old matrix product. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator
open scoped BigOperators Classical

section General

variable {O E W : Type*} (A : O→Type*) [Fintype O] [∀ o,Fintype (A o)]
  [Fintype E] [Fintype W]

theorem placed_row_by_variable (P : Placement E W (OrbitSlots A)) (y : W→ℚ)
    (q : OrbitSlots A→ℚ) :
    (∑ s,q s*(embeddingMatrix A P).mulVec y s) =
      ∑ w,(∑ s∈filled P w,q s)*y w := by
  unfold Matrix.mulVec dotProduct
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.sum_mul]
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
  · intro s hs
    simp [embeddingMatrix,(Finset.mem_sdiff.mp hs).2]
  · intro s hs
    simp [embeddingMatrix,hs]

end General

variable {E W F Copy I B : Type*} [Fintype E] [Fintype W] [Fintype Copy]
  [Fintype I] [Fintype B] [LinearOrder B]

set_option maxHeartbeats 2600000 in
theorem sourceTuple_read_coordinate (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (i : I) (g : B) (x : W→Bool) (r : NativeRows keep Copy I B) :
    qRead (CoordFamily (Copy:=Copy) (I:=I) (B:=B))
      (place L (nativeMask L i g x)) r.val=sourceTuple keep L i x g r := by
  let A := CoordFamily (Copy:=Copy) (I:=I) (B:=B)
  calc
    _ = ∑ w,(∑ s∈filled L.orbitPlacement w,qOrbitRow A r.val s)*nativeMask L i g x w :=
      placed_row_by_variable A L.orbitPlacement (nativeMask L i g x) (qOrbitRow A r.val)
    _ = _ := by
      unfold sourceTuple exceptionalMatrix
      rw [Matrix.mulVec,dotProduct]
      simp_rw [rawMeasurement_apply]
      apply Finset.sum_congr rfl
      intro w _
      simp [A,nativeMask,qbits]

set_option maxHeartbeats 2300000 in
theorem sourceTuple_total_read (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (i : I) (x : W→Bool) (r : NativeRows keep Copy I B) :
    qRead (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) (place L (qbits x)) r.val =
      ∑ g,sourceTuple keep L i x g r := by
  let A := CoordFamily (Copy:=Copy) (I:=I) (B:=B)
  calc
    _ = qRead A (place L (∑ g,nativeMask L i g x)) r.val :=
      congrArg (fun y=>qRead A (place L y) r.val) (group_mask_sum L i x).symm
    _ = ∑ g,qRead A (place L (nativeMask L i g x)) r.val := by
      unfold qRead place
      rw [Matrix.mulVec_sum]
      simp_rw [Finset.sum_apply,Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := Finset.sum_congr rfl (fun g _=>sourceTuple_read_coordinate keep L i g x r)

def FixesExceptionalReads (keep : ℕ→Prop) (M : Mix Copy I B) : Prop :=
  ∀ ζ : Vec Copy I B,
    (∀ r : NativeRows keep Copy I B,
      qRead (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) ζ r.val=0) → M.mulVec ζ=ζ

set_option maxHeartbeats 4000000 in
theorem placed_read_implements_base (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (M : Mix Copy I B) (hM : FixesExceptionalReads keep M) :
    ActualBaseInvariant keep L M := by
  intro i x y hy s
  let A := CoordFamily (Copy:=Copy) (I:=I) (B:=B)
  let a := place L (qbits x)
  let b := place L (qbits y)
  have hq (r : NativeRows keep Copy I B) : qRead A (a-b) r.val=0 := by
    have hSub : qRead A (a-b) r.val=qRead A a r.val-qRead A b r.val := by
      unfold qRead
      simp only [Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
    rw [hSub,sourceTuple_total_read keep L i x r,sourceTuple_total_read keep L i y r,hy,sub_self]
  have hf := hM (a-b) hq
  rw [Matrix.mulVec_sub] at hf
  have hh := congrFun hf s
  change M.mulVec a s-M.mulVec b s=a s-b s at hh
  change a s-M.mulVec a s=b s-M.mulVec b s
  linarith only [hh]

#print axioms placed_row_by_variable
#print axioms sourceTuple_read_coordinate
#print axioms sourceTuple_total_read
#print axioms placed_read_implements_base
end P5MainBalance.M6
