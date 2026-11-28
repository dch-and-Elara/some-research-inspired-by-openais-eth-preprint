import V8CapacitySmithModules
import V8CapacityLift

/-! Paper 6/v8 U1: the attainable module in the original ambient row
coordinates, with the actual decoder-column iff, before choosing any
Smith chart. All reduction and lifting is in the scalar base DVR. -/
namespace V8CapacityUnified
open scoped Classical
open V8CapacityCRTJet V8CapacitySmith V8CapacityLift

noncomputable section
set_option linter.unusedSectionVars false

variable {O X Y : Type*} [CommRing O]

/-- Pointwise reduction in the physical sender coordinate chart. -/
def residueRows (π : O) (p : ℕ) : (X → O) →ₗ[O] (X → BaseMod O π p) :=
  LinearMap.pi fun x => (Algebra.linearMap O _).comp (LinearMap.proj x)

@[simp] theorem residueRows_apply (π : O) (p : ℕ) (v : X → O) (x : X) :
    residueRows π p v x=coeffMod O π p (v x) := rfl

theorem residueRows_surj (π : O) (p : ℕ) :
    Function.Surjective (residueRows (X:=X) π p) := by
  intro v
  choose x hx using fun i : X => Ideal.Quotient.mk_surjective (v i)
  exact ⟨x,funext hx⟩

theorem residues_eq_iff (π : O) (p : ℕ) (x y : O) :
    coeffMod O π p x=coeffMod O π p y ↔ π^p∣x-y := by
  change Ideal.Quotient.mk (Ideal.span ({π^p}:Set O)) x=
    Ideal.Quotient.mk (Ideal.span ({π^p}:Set O)) y ↔ _
  rw [← sub_eq_zero,← map_sub,Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]

/-- Integral rows in the scaled lattice π⁻ᴸE. This is independent of p. -/
def dividedLattice (π : O) (L : ℕ) (E : Submodule O (X → O)) :
    Submodule O (X → O) :=
  E.comap (π^L • LinearMap.id)

theorem divided_mem (π : O) (L : ℕ) (E : Submodule O (X → O)) (v : X → O) :
    v∈dividedLattice π L E ↔ (π^L:O) • v∈E := Iff.rfl

/-- The quotient of the sum with πᵖOˣ in U1, embedded in the actual
ambient quotient using ordinary row reduction. -/
def attainable (π : O) (L p : ℕ) (E : Submodule O (X → O)) :
    Submodule O (X → BaseMod O π p) :=
  (dividedLattice π L E).map (residueRows π p)

theorem U1_lift (π : O) (L p : ℕ) (E : Submodule O (X → O)) (v : X → O) :
    residueRows π p v∈attainable π L p E ↔ realizable π L p E v := by
  change (∃ x, x∈dividedLattice π L E ∧ residueRows π p x=residueRows π p v) ↔ _
  constructor
  · rintro ⟨x,hx,hxv⟩
    have h (i : X) := (residues_eq_iff π p (x i) (v i)).mp (congrFun hxv i)
    choose d hd using h
    have he : v+(π^p:O)•d=x := by
      funext i
      have hh := hd i
      change v i+π^p*d i=x i
      rw [← hh]
      ring
    exact ⟨d,by rw [he]; exact (divided_mem π L E x).mp hx⟩
  · rintro ⟨d,hd⟩
    use v+(π^p:O)•d
    refine ⟨(divided_mem π L E _).mpr hd,?_⟩
    funext i
    apply (residues_eq_iff π p _ _).mpr
    exact ⟨d i,by change v i+π^p*d i-v i=π^p*d i; ring⟩

/-- Genuine same-row, same-decoder feasibility. The only coverage
hypothesis is the exact image of the legal numerator map. -/
theorem U1_numerator_iff {G : Type*} (π : O) (L p : ℕ)
    (E : Submodule O (X → O)) (read : G → X → O)
    (hE : Set.range read=↑E) (target : X → O) :
    residueRows π p target∈attainable π L p E ↔
      ∃ g, ∀ x, π^(L+p)∣read g x-π^L*target x := by
  rw [U1_lift]
  constructor
  · rintro ⟨d,hd⟩
    have hm : (π^L:O)•(target+(π^p:O)•d) ∈ Set.range read := by
      rw [hE]
      exact hd
    obtain ⟨g,hg⟩ := hm
    refine ⟨g,fun x => ⟨d x,?_⟩⟩
    simp only [hg,Pi.smul_apply,Pi.add_apply,smul_eq_mul,pow_add]
    ring
  · rintro ⟨g,hg⟩
    choose d hd using hg
    refine ⟨d,?_⟩
    have he : (π^L:O)•(target+(π^p:O)•d)=read g := by
      funext i
      have hh := hd i
      rw [pow_add] at hh
      change π^L*(target i+π^p*d i)=read g i
      linear_combination -hh
    rw [he]
    have h : read g ∈ Set.range read := ⟨g,rfl⟩
    rwa [hE] at h

theorem U1_receiver_columns {G : Type*} (π : O) (L p : ℕ)
    (E : Submodule O (X → O)) (read : G → X → O)
    (hE : Set.range read=↑E) (target : Y → X → O) :
    (∃ recv : Y → G, ∀ y x, π^(L+p)∣read (recv y) x-π^L*target y x) ↔
      ∀ y, residueRows π p (target y)∈attainable π L p E := by
  constructor
  · rintro ⟨recv,hr⟩ y
    exact (U1_numerator_iff π L p E read hE (target y)).mpr ⟨recv y,hr y⟩
  · intro ht
    choose recv hr using fun y => (U1_numerator_iff π L p E read hE (target y)).mp (ht y)
    exact ⟨recv,hr⟩

variable {K : Type*} [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]

/-- Literally the fraction-field scaled lattice, intersected with
integral ambient rows before finite reduction. -/
theorem U1_fraction_divided (π : O) (hπ : π≠0) (L : ℕ) (E : Submodule O (X → O))
    (v : X → O) :
    v∈dividedLattice π L E ↔
      ∃ e : E, ∀ x, algebraMap O K (v x) =
        algebraMap O K (e.val x) / (algebraMap O K (π^L)) := by
  have hd : algebraMap O K (π^L) ≠ 0 := by
    exact (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr (pow_ne_zero _ hπ)
  rw [divided_mem]
  constructor
  · intro hv
    refine ⟨⟨_,hv⟩,fun x => (eq_div_iff hd).mpr ?_⟩
    change algebraMap O K (v x) * algebraMap O K (π^L)=algebraMap O K (π^L*v x)
    rw [map_mul,mul_comm]
  · rintro ⟨e,he⟩
    have h : (π^L:O)•v=e.val := by
      funext x
      apply IsFractionRing.injective O K
      change algebraMap O K (π^L*v x)=_
      rw [map_mul,mul_comm]
      exact (eq_div_iff hd).mp (he x)
    exact h ▸ e.property

#print axioms residueRows_surj
#print axioms residues_eq_iff
#print axioms U1_lift
#print axioms U1_numerator_iff
#print axioms U1_receiver_columns
#print axioms U1_fraction_divided
end
end V8CapacityUnified
