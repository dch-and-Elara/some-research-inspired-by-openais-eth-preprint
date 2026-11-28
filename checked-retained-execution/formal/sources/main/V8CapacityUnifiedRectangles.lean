import V8CapacityUnifiedHybrid

/-! Rectangular fiber masks for U7. Zero extension is represented as
explicit matrix multiplication by row and column incidence matrices. -/
namespace V8CapacityUnified.U7
open scoped Classical BigOperators

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000

variable {K X Y : Type*} [Field K] [Fintype X] [Fintype Y]
variable (P : X → Prop) (Q : Y → Prop) [DecidablePred P] [DecidablePred Q]

local notation "L" => {x // P x}
local notation "R" => {y // Q y}

def rowInclusion : Matrix X L K := Matrix.of fun i u => if i=u.val then 1 else 0

def colInclusion : Matrix R Y K := Matrix.of fun v j => if v.val=j then 1 else 0

def extend (A : Matrix L R K) : Matrix X Y K :=
  (rowInclusion P * A) * colInclusion Q

theorem extend_rank (A : Matrix L R K) : (extend P Q A).rank≤A.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

theorem row_restrict_in (A : Matrix L R K) (x : X) (hx : P x) (v : R) :
    (rowInclusion P*A : Matrix X R K) x v=A ⟨x,hx⟩ v := by
  rw [Matrix.mul_apply,Finset.sum_eq_single_of_mem ⟨x,hx⟩ (Finset.mem_univ _) ]
  · simp [rowInclusion]
  · intro x' _ hne
    have h : x≠x'.val := fun he => hne (Subtype.ext he.symm)
    simp [rowInclusion,h]

theorem row_restrict_out (A : Matrix L R K) (x : X) (hx : ¬ P x) (v : R) :
    (rowInclusion P*A : Matrix X R K) x v=0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro u _
  have h : x≠u.val := fun he => hx (he.symm ▸ u.property)
  simp [rowInclusion,h]

theorem extend_on (A : Matrix L R K) (x : X) (y : Y) (hx : P x) (hy : Q y) :
    extend P Q A x y=A ⟨x,hx⟩ ⟨y,hy⟩ := by
  rw [extend,Matrix.mul_apply,Finset.sum_eq_single_of_mem ⟨y,hy⟩ (Finset.mem_univ _)]
  · rw [row_restrict_in P Q A x hx]
    simp [colInclusion]
  · intro y' _ hne
    have h : y'.val≠y := fun he => hne (Subtype.ext he)
    simp [colInclusion,h]

theorem extend_zero_left (A : Matrix L R K) (x : X) (y : Y) (hx : ¬ P x) :
    extend P Q A x y=0 := by
  simp only [extend,Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro v _
  change (∑ u : L, (rowInclusion P) x u*A u v)*(colInclusion Q) v y=0
  rw [← Matrix.mul_apply,row_restrict_out P Q A x hx,zero_mul]

theorem extend_zero_right (A : Matrix L R K) (x : X) (y : Y) (hy : ¬ Q y) :
    extend P Q A x y=0 := by
  rw [extend,Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro v _
  have h : v.val≠y := fun he => hy (he ▸ v.property)
  simp [colInclusion,h]

variable {T : Type*} [Fintype T]
variable (rows : T → X → Prop) (cols : T → Y → Prop)
variable [∀ t, DecidablePred (rows t)] [∀ t, DecidablePred (cols t)]

def fiberSum (a : ∀ t, Matrix {x // rows t x} {y // cols t y} K) : Matrix X Y K :=
  ∑ t, extend (rows t) (cols t) (a t)

theorem fiberSum_rank (a : ∀ t, Matrix {x // rows t x} {y // cols t y} K)
    (H : ℕ) (h : ∀ t, (a t).rank≤H) :
    (fiberSum rows cols a).rank≤Fintype.card T*H := by
  unfold fiberSum
  apply (rank_sum_le Finset.univ _).trans
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] using
    Finset.sum_le_sum (s:=Finset.univ) (g:=fun _ : T => H)
      (fun t _ => (extend_rank (rows t) (cols t) (a t)).trans (h t))

theorem fiberSum_on (a : ∀ t, Matrix {x // rows t x} {y // cols t y} K)
    (x : X) (y : Y) (t : T) (hx : rows t x) (hy : cols t y)
    (other : ∀ s, s≠t → ¬ rows s x ∨ ¬ cols s y) :
    fiberSum rows cols a x y=a t ⟨x,hx⟩ ⟨y,hy⟩ := by
  rw [fiberSum,Matrix.sum_apply,Finset.sum_eq_single_of_mem t (Finset.mem_univ _)]
  · exact extend_on (rows t) (cols t) (a t) x y hx hy
  · intro s _ hs
    rcases other s hs with hx'|hy'
    · exact extend_zero_left (rows s) (cols s) (a s) x y hx'
    · exact extend_zero_right (rows s) (cols s) (a s) x y hy'

#print axioms extend_rank
#print axioms extend_on
#print axioms extend_zero_left
#print axioms extend_zero_right
#print axioms fiberSum_rank
#print axioms fiberSum_on
end
end V8CapacityUnified.U7
