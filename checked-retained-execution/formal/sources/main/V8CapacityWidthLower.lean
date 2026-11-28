import V8CapacityGenerator

/-! The A3 lower bound is valid for actual factorizations through the
truncated coefficient ring, not just for linear expressions whose
summands happen to lie in the attainable module. -/
namespace V8CapacityWidthLower
open scoped Classical BigOperators
open Module V8CapacityCRTJet V8CapacityGenerator

noncomputable section

variable {O M I J : Type*} [CommRing O] [IsDomain O]
variable [IsPrincipalIdealRing O] [AddCommGroup M] [Module O M]
variable [Fintype I] [Fintype J]

/-- The PID pullback proves the bounded-generator claim even when the
outer containing module has torsion. -/
theorem bounded_generators_of_submodule (T : Submodule O M)
    (A : (J → O) →ₗ[O] M) (containment : T ≤ LinearMap.range A) :
    ∃ r ≤ Fintype.card J, ∃ v : Fin r → T,
      ∀ x : T, ∃ c : Fin r → O, x=∑ i, c i • v i := by
  let P := Submodule.comap A T
  obtain ⟨r,S⟩ := P.smithNormalForm (Pi.basisFun O J)
  let G : P →ₗ[O] T := (A.comp P.subtype).codRestrict T (fun y => y.property)
  refine ⟨r,(by simpa using Fintype.card_le_of_injective S.f S.f.injective),
    fun i => G (S.bN i),?_⟩
  intro x
  obtain ⟨y,hy⟩ := containment x.property
  let z : P := ⟨y,by change A y∈T; rw [hy]; exact x.property⟩
  have hz : G z=x := Subtype.ext hy
  refine ⟨fun i => S.bN.repr z i,?_⟩
  simpa only [map_sum,map_smul,hz] using (congrArg G (S.bN.sum_repr z)).symm

variable [IsLocalRing O]

/-- A product of nonzero cyclic factors contained in the image of an
r-column linear map over O requires at least that many columns. -/
theorem embedded_cyclic_requires (π : O) (hz : IsLocalRing.residue O π=0)
    (t : I → ℕ) (ht : ∀ i, 0<t i)
    (B : ((i : I) → BaseMod O π (t i)) →ₗ[O] M) (hB : Function.Injective B)
    (A : (J → O) →ₗ[O] M) (containment : LinearMap.range B ≤ LinearMap.range A) :
    Fintype.card I≤Fintype.card J := by
  obtain ⟨r,hr,vs,hvs⟩ := bounded_generators_of_submodule (LinearMap.range B) A containment
  choose w hw using (fun i : Fin r => (vs i).property)
  have gen : ∀ x : (i : I) → BaseMod O π (t i), ∃ c : Fin r → O, x=∑ i, c i • w i := by
    intro x
    let y : LinearMap.range B := ⟨B x,⟨x,rfl⟩⟩
    obtain ⟨c,hc⟩ := hvs y
    refine ⟨c,hB ?_⟩
    have h := congrArg (fun u : LinearMap.range B => (u:M)) hc
    change B x = _ at h
    simpa only [map_sum,map_smul,hw,Submodule.coe_sum,Submodule.coe_smul] using h
  exact (generators_at_least π hz t ht w gen).trans (by simpa using hr)

/-- Integral coefficients span every residue word, so any claimed
factorization through r residue coordinates bounds the size of any
nonzero cyclic product embedded in that matrix's image. -/
theorem residue_embedded_cyclic_width (π : O) (hz : IsLocalRing.residue O π=0)
    (t : I → ℕ) (ht : ∀ i, 0<t i) (p : ℕ)
    (B : ((i : I) → BaseMod O π (t i)) →ₗ[O] M) (hB : Function.Injective B)
    [Module (BaseMod O π p) M] [IsScalarTower O (BaseMod O π p) M]
    (A : (J → BaseMod O π p) →ₗ[BaseMod O π p] M)
    (containment : ∀ x, ∃ z, A z=B x) : Fintype.card I≤Fintype.card J := by
  let red : (J → O) →ₗ[O] (J → BaseMod O π p) :=
    LinearMap.pi fun j => (Algebra.linearMap O (BaseMod O π p)).comp (LinearMap.proj j)
  apply embedded_cyclic_requires π hz t ht B hB ((A.restrictScalars O).comp red)
  rintro b ⟨x,rfl⟩
  obtain ⟨z,hz⟩ := containment x
  choose z' hz' using (fun j => Ideal.Quotient.mk_surjective (z j))
  refine ⟨z',?_⟩
  have he : red z'=z := by
    funext j
    exact hz' j
  change A (red z')=B x
  rw [he,hz]

#print axioms bounded_generators_of_submodule
#print axioms embedded_cyclic_requires
#print axioms residue_embedded_cyclic_width
end
end V8CapacityWidthLower

