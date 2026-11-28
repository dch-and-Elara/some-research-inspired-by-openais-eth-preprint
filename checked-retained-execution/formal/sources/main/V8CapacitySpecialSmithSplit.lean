import V8CapacitySpecialSplit

/-! The actual chosen Smith chart gives a second split presentation of
the same submodule, which lets us compare full valuation profiles. -/
namespace V8CapacitySpecialSplit
open scoped Classical BigOperators
open V8CapacitySmith Module

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 700000

variable {O I J : Type*} [CommRing O] [IsDomain O] [Fintype I]

def place (e : J ↪ I) : (J → O) →ₗ[O] (I → O) :=
  LinearMap.pi fun i => if h : i∈Set.range e then LinearMap.proj (Classical.choose h) else 0

theorem place_image (e : J ↪ I) (x : J → O) (j : J) :
    place e x (e j)=x j := by
  have he : e j∈Set.range e := ⟨j,rfl⟩
  have hi : Classical.choose he=j := e.injective (Classical.choose_spec he)
  simp only [place,LinearMap.pi_apply,dif_pos he,LinearMap.proj_apply,hi]

theorem place_else (e : J ↪ I) (x : J → O) (i : I) (hi : i∉Set.range e) :
    place e x i=0 := by
  simp only [place,LinearMap.pi_apply,dif_neg hi,LinearMap.zero_apply]

variable {π : O} {N : Submodule O (I → O)} {n : ℕ}
variable (S : Powered π N I n)

theorem equivFun_is_coord (x : I → O) (i : I) :
    S.chart.bM.equivFun x i=coord S x i := rfl

def smithEmbedding : (Fin n → O) →ₗ[O] (I → O) :=
  S.chart.bM.equivFun.symm.toLinearMap.comp (place S.chart.f)

def smithProject : (I → O) →ₗ[O] (Fin n → O) :=
  LinearMap.pi fun j => ((LinearMap.proj (S.chart.f j)).comp S.chart.bM.equivFun.toLinearMap)

theorem smith_embedding_receipt (v : Fin n → O) (i : I) :
    coord S (smithEmbedding S v) i=place S.chart.f v i := by
  rw [← equivFun_is_coord]
  change S.chart.bM.equivFun (S.chart.bM.equivFun.symm (place S.chart.f v)) i=_
  rw [LinearEquiv.apply_symm_apply]

theorem smith_project_receipt (x : I → O) (j : Fin n) :
    smithProject S x j=coord S x (S.chart.f j) := rfl

def fromSmith : Split π N (Fin n) where
  embed := smithEmbedding S
  proj := smithProject S
  left x := by
    funext j
    rw [smith_project_receipt,smith_embedding_receipt,place_image]
  exp := S.exponent
  chart x := by
    rw [exact_membership S x]
    constructor
    · rintro ⟨hd,hz⟩
      choose w hw using hd
      refine ⟨w, S.chart.bM.equivFun.injective ?_⟩
      funext i
      simp only [equivFun_is_coord,smith_embedding_receipt]
      by_cases hi : i∈Set.range S.chart.f
      · obtain ⟨j,rfl⟩ := hi
        rw [place_image,hw j]
      · rw [place_else _ _ _ hi,hz i hi]
    · rintro ⟨w,rfl⟩
      constructor
      · intro j
        rw [smith_embedding_receipt,place_image]
        exact dvd_mul_right _ _
      · intro i hi
        rw [smith_embedding_receipt,place_else _ _ _ hi]

#print axioms place_image
#print axioms smith_embedding_receipt
#print axioms fromSmith
end
end V8CapacitySpecialSplit

