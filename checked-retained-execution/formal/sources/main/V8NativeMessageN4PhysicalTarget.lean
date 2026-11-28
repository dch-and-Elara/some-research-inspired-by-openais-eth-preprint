import V8NativeMessageN4PhysicalCut
import V8CapacityUnifiedMatching
import P5D1LiteralCount

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3550000

/-! Restrict the original pinned positive-OR four-copy formula, hence
also its actual old-row D file, to the generated induced matching.
The off-matching signs are TRUE, unlike C2's availability chart. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open V8CapacityUnified.U7 Paper5.HybridClosure Paper5.D1Literal J6R9Recursive J6R10Repack
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W] {F : Finset (W×W)}
variable {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]} {m : ℕ}

def restriction (M : Pairs (storageGraph F) m) (x y : Fin m→Bool) (v : W) : Bool :=
  if h : v∈Set.range M.seat then
    let j := Classical.choose h
    if j.2 then y j.1 else x j.1
  else true

omit [Fintype W] in
theorem restriction_on (M : Pairs (storageGraph F) m)
    (x y : Fin m→Bool) (q : Fin m×Bool) :
    restriction M x y (M.seat q)=(if q.2 then y q.1 else x q.1) := by
  have h : M.seat q∈Set.range M.seat := ⟨q,rfl⟩
  have e : Classical.choose h=q := M.seat.injective (Classical.choose_spec h)
  simp only [restriction,dif_pos h,e]

omit [Fintype W] in
theorem restriction_off (M : Pairs (storageGraph F) m)
    (x y : Fin m→Bool) (v : W) (h : v∉Set.range M.seat) : restriction M x y v=true :=
  dif_neg h

def nativeCount (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3) (s : W→Bool) : ℕ :=
  PinnedCNF.modelCount (MainClonedCNF.formula F (MainClonedCNF.leftSlot F reg)
    (MainClonedCNF.rightSlot F reg) s)

omit [Fintype W] in
theorem original_OR_iff (M : Pairs (storageGraph F) m) (x y : Fin m→Bool) :
    PinnedCNF.AllEdges F (restriction M x y) ↔ ∀ j, x j=true ∨ y j=true := by
  constructor
  · intro hall j
    have h := hall (M.edge j).val (M.edge j).property
    have hl := M.left j
    have hr := M.right j
    cases hz : M.reverse j
    · simp only [hz,Bool.not_false] at hl hr
      change (M.edge j).val.1=M.seat (j,false) at hl
      change (M.edge j).val.2=M.seat (j,true) at hr
      simpa only [hl,hr,restriction_on,Bool.false_eq_true,if_false,if_true] using h
    · simp only [hz,Bool.not_true] at hl hr
      change (M.edge j).val.2=M.seat (j,false) at hl
      change (M.edge j).val.1=M.seat (j,true) at hr
      rw [hl,hr,restriction_on,restriction_on] at h
      exact h.symm
  · intro h e he
    by_cases hu : e.1∈Set.range M.seat
    · by_cases hv : e.2∈Set.range M.seat
      · obtain ⟨⟨j,a⟩,hj⟩ := hu
        obtain ⟨⟨k,b⟩,hk⟩ := hv
        have hs := M.only ⟨e,he⟩ (j,a) (k,b) hj.symm hk.symm
        obtain ⟨hjk,hab⟩ := hs
        change j=k at hjk
        subst k
        rw [← hj,← hk,restriction_on,restriction_on]
        cases a <;> cases b
        · exact (hab rfl).elim
        · exact h j
        · exact (h j).symm
        · exact (hab rfl).elim
      · exact Or.inr (restriction_off M x y _ hv)
    · exact Or.inl (restriction_off M x y _ hu)

theorem literal_count_on_matching (M : Pairs (storageGraph F) m) (x y : Fin m→Bool) :
    nativeCount F reg (restriction M x y)=∏ j : Fin m, if x j||y j then 1 else 0 := by
  unfold nativeCount
  rw [MainClonedCNF.modelCount_cloned,PinnedCNF.count_eq_indicator,original_OR_iff]
  by_cases h : ∀ j : Fin m, x j=true ∨ y j=true
  · rw [if_pos h]
    symm
    apply Finset.prod_eq_one
    intro j _
    simp only [Bool.or_eq_true,if_pos (h j)]
  · rw [if_neg h]
    obtain ⟨j,hj⟩ := not_forall.mp h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by
      simp only [Bool.or_eq_true,if_neg hj])

theorem literal_count_scalar {R : Type*} [CommRing R]
    (M : Pairs (storageGraph F) m) (x y : Fin m→Bool) :
    (nativeCount F reg (restriction M x y):R)=matchingTarget R m x y := by
  rw [literal_count_on_matching]
  simp only [matchingTarget,Matrix.of_apply,pairOR,Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro j _
  split <;> simp

theorem old_row_D_terminal_ON (hf : f.Monic) (M : Pairs (storageGraph F) m) (x y : Fin m→Bool) :
    let p₀ := 4*Fintype.card W+1
    reduce p₀ f 1 (trueContraction (dNetwork F reg) (oldRowFile F reg f p₀ (restriction M x y)) hf) =
      matchingTarget (Residue f 1 p₀) m x y := by
  dsimp only
  exact (oldRow_contraction_reduce F reg f hf _ _).trans (literal_count_scalar M x y)

variable {O L : Type*} [CommRing O] [Field L] [Algebra O L]

/-- Any correct integral lift of the restriction has full rank, since
the residue matrix is the tensor OR matrix, not the C2 identity. -/
theorem matching_lift_rank (M : Pairs (storageGraph F) m)
    (χ : O→+*ZMod 2) (hinj : Function.Injective (algebraMap O L))
    (A : Matrix (Fin m→Bool) (Fin m→Bool) L)
    (hc : ∀ x y, ∃ o : O, algebraMap O L o=A x y ∧
      χ o=(nativeCount F reg (restriction M x y):ZMod 2)) :
    A.rank=2^m := by
  choose a ha using hc
  let B : Matrix (Fin m→Bool) (Fin m→Bool) O := Matrix.of a
  have hL : B.map (algebraMap O L)=A := by ext x y; exact (ha x y).1
  have h₂ : B.map χ=matchingTarget (ZMod 2) m := by
    ext x y
    exact (ha x y).2.trans (literal_count_scalar M x y)
  have hχ : χ B.det≠0 := by
    have e : χ B.det=(B.map χ).det := RingHom.map_det χ B
    rw [e,h₂]
    exact matching_det_ne_zero (ZMod 2) m
  have hB : B.det≠0 := by intro hz; exact hχ (by simp [hz])
  have hA : A.det≠0 := by
    have e : algebraMap O L B.det=(B.map (algebraMap O L)).det := RingHom.map_det (algebraMap O L) B
    rw [← hL,← e]
    exact (map_ne_zero_iff _ hinj).mpr hB
  rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr
    (isUnit_iff_ne_zero.mpr hA))]
  simp

#print axioms restriction_on
#print axioms restriction_off
#print axioms original_OR_iff
#print axioms literal_count_on_matching
#print axioms literal_count_scalar
#print axioms old_row_D_terminal_ON
#print axioms matching_lift_rank
end
end V8NativeMessage.N4
