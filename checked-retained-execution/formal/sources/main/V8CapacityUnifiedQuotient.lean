import V8CapacityUnifiedObservation

/-! Literal quotient-of-a-sum form of U1. The quotient submodule is
πᵖ times the physical ambient lattice, not just the congruence kernel
on the numerator module. -/
namespace V8CapacityUnified
open scoped Classical
open V8CapacityCRTJet

noncomputable section
set_option linter.unusedSectionVars false

variable {O X : Type*} [CommRing O] (π : O) (p : ℕ)

def precisionLattice : Submodule O (X → O) :=
  LinearMap.range (π^p • LinearMap.id)

theorem precisionLattice_kernel :
    precisionLattice (X:=X) π p=LinearMap.ker (residueRows π p) := by
  ext v
  rw [LinearMap.mem_ker]
  change (∃ d : X → O, (π^p:O) • d=v) ↔ _
  constructor
  · rintro ⟨d,rfl⟩
    funext x
    change coeffMod O π p (π^p*d x)=0
    have h := (residues_eq_iff π p (π^p*d x) 0).mpr (by rw [sub_zero]; exact dvd_mul_right _ _)
    simpa only [map_zero] using h
  · intro h
    have key (x : X) : π^p∣v x := by
      rw [← sub_zero (v x)]
      apply (residues_eq_iff π p (v x) 0).mp
      simpa only [residueRows_apply,Pi.zero_apply,map_zero] using congrFun h x
    choose d hd using key
    exact ⟨d,funext (fun x => (hd x).symm)⟩

variable (L : ℕ) (E : Submodule O (X → O))

def U1sum : Submodule O (X → O) := dividedLattice π L E ⊔ precisionLattice π p

def U1denominator : Submodule O (U1sum π p L E) :=
  (precisionLattice π p).comap (U1sum π p L E).subtype

def U1quotientMap : U1sum π p L E →ₗ[O] attainable π L p E where
  toFun x := ⟨residueRows π p x.val,by
    obtain ⟨a,ha,b,hb,h⟩ := Submodule.mem_sup.mp x.property
    have hb0 : residueRows π p b=0 := by
      rw [precisionLattice_kernel] at hb
      exact LinearMap.mem_ker.mp hb
    refine ⟨a,ha,?_⟩
    rw [← h,map_add,hb0,add_zero]⟩
  map_add' _ _ := by ext i; simp
  map_smul' a v := by
    apply Subtype.ext
    exact map_smul (residueRows π p) a v.val

theorem U1quotientMap_surjective : Function.Surjective (U1quotientMap π p L E) := by
  intro x
  obtain ⟨a,ha,hx⟩ := x.property
  refine ⟨⟨a,(show dividedLattice π L E≤U1sum π p L E from le_sup_left) ha⟩,?_⟩
  exact Subtype.ext hx

theorem U1quotientMap_ker :
    LinearMap.ker (U1quotientMap π p L E)=U1denominator π p L E := by
  ext x
  rw [LinearMap.mem_ker,U1denominator,Submodule.mem_comap,precisionLattice_kernel,
    LinearMap.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

def U1_exact_ambient_quotient :
    (U1sum π p L E ⧸ U1denominator π p L E) ≃ₗ[O] attainable π L p E := by
  rw [← U1quotientMap_ker π p L E]
  exact LinearMap.quotKerEquivOfSurjective (U1quotientMap π p L E)
    (U1quotientMap_surjective π p L E)

#print axioms precisionLattice_kernel
#print axioms U1quotientMap_surjective
#print axioms U1quotientMap_ker
#print axioms U1_exact_ambient_quotient
end
end V8CapacityUnified
