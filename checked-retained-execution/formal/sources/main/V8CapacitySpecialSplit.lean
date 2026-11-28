import V8CapacityNativeA3
import V8CapacityWidthRank

/-! A split diagonal presentation of an actual image. Its exponents are
recovered by reducing each saturation layer modulo the maximal ideal;
the "chosen Smith form" need not have been an ordered presentation. -/
namespace V8CapacitySpecialSplit
open scoped Classical BigOperators
open Module V8CapacitySmith

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 950000

variable {O I J : Type*} [CommRing O] [IsDomain O]

theorem pow_mul_iff (π : O) (hπ : π≠0) (b d : ℕ) (x : O) :
    π^d∣π^b*x ↔ π^(d-b)∣x := by
  by_cases h : b≤d
  · calc
      _ ↔ (π^b*π^(d-b))∣π^b*x := by rw [← pow_add,Nat.add_sub_of_le h]
      _ ↔ _ := mul_dvd_mul_iff_left (pow_ne_zero _ hπ)
  · have hd : d≤b := Nat.le_of_not_ge h
    rw [Nat.sub_eq_zero_of_le hd,pow_zero]
    constructor
    · intro _
      exact one_dvd _
    · intro _
      exact dvd_mul_of_dvd_left (pow_dvd_pow π hd) _

structure Split (π : O) (N : Submodule O (I → O)) (J : Type*) where
  embed : (J → O) →ₗ[O] (I → O)
  proj : (I → O) →ₗ[O] (J → O)
  left : Function.LeftInverse proj embed
  exp : J → ℕ
  chart : ∀ x : I → O, x∈N ↔ ∃ w : J → O, x=embed (fun i => π^exp i*w i)

variable {π : O} {N : Submodule O (I → O)} (S : Split π N J)

theorem sat_iff (hπ : π≠0) (b : ℕ) (x : I → O) :
    (π^b:O) • x∈N ↔ S.embed (S.proj x)=x ∧
      ∀ j, π^(S.exp j-b)∣S.proj x j := by
  constructor
  · intro hx
    obtain ⟨w,hw⟩ := (S.chart _).mp hx
    have he := congrArg S.proj hw
    rw [map_smul,S.left] at he
    constructor
    · have eq : (π^b:O) • S.embed (S.proj x)=(π^b:O) • x := by
        rw [← map_smul,he,← hw]
      funext i
      exact mul_left_cancel₀ (pow_ne_zero _ hπ) (congrFun eq i)
    · intro j
      apply (pow_mul_iff π hπ b (S.exp j) _).mp
      refine ⟨w j,?_⟩
      exact congrFun he j
  · rintro ⟨he,hw⟩
    choose w hx using (fun j => (pow_mul_iff π hπ b (S.exp j) _).mpr (hw j))
    apply (S.chart _).mpr
    refine ⟨w,?_⟩
    have h' : (fun j => π^S.exp j*w j)=(π^b:O) • (S.proj x) := by
      funext j
      exact (hx j).symm
    rw [h',map_smul,he]

variable [Fintype I] [Fintype J]

def matrixSplit (π : O) (A G : Matrix I J O) (R : Matrix J I O) (d : J → ℕ)
    (hs : R*G=1) (hd : A=G*Matrix.diagonal (fun j => π^d j)) :
    Split π (matrixImage A) J where
  embed := G.mulVecLin
  proj := R.mulVecLin
  left x := by
    change R.mulVec (G.mulVec x)=x
    rw [Matrix.mulVec_mulVec,hs,Matrix.one_mulVec]
  exp := d
  chart x := by
    constructor
    · rintro ⟨a,rfl⟩
      refine ⟨a,?_⟩
      change A.mulVec a=G.mulVec _
      rw [hd,← Matrix.mulVec_mulVec]
      congr 1
      funext j
      exact Matrix.mulVec_diagonal _ _ _
    · rintro ⟨a,rfl⟩
      refine ⟨a,?_⟩
      change A.mulVec a=G.mulVec _
      rw [hd,← Matrix.mulVec_mulVec]
      congr 1
      funext j
      exact Matrix.mulVec_diagonal _ _ _

#print axioms pow_mul_iff
#print axioms sat_iff
#print axioms matrixSplit
end
end V8CapacitySpecialSplit

