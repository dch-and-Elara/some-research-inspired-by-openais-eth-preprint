import V8CapacitySmith
import V8CapacityCyclic

/-! Observable-column membership after the actual Smith coordinate
change. In each present coordinate exactly the clipped residual exponent
is required; every absent coordinate is zero modulo π^p. -/
namespace V8CapacitySmith
open scoped BigOperators Classical
open Module V8CapacityCyclic

noncomputable section
set_option linter.unusedSectionVars false

variable {O M I : Type*} [CommRing O] [IsDomain O]
variable [AddCommGroup M] [Module O M] [Fintype I]
variable {π : O} {N : Submodule O M} {n : ℕ}
variable (S : Powered π N I n)

def coord (x : M) (j : I) : O := S.chart.bM.repr x j

def fromCoord (z : I → O) : M :=
  S.chart.bM.repr.symm (Finsupp.equivFunOnFinite.symm z)

theorem coord_fromCoord (z : I → O) (j : I) : coord S (fromCoord S z) j=z j := by
  simp [coord,fromCoord]

theorem coord_scale_add (x e : M) (u v : O) (j : I) :
    coord S (u • (x+v • e)) j = u*(coord S x j + v*coord S e j) := by
  simp [coord,mul_add]

theorem on_image_coordinate (x : N) (i : Fin n) :
    coord S (x:M) (S.chart.f i)=S.chart.a i*(S.chart.bN.repr x i) := by
  simpa only [coord,Function.comp_apply,Pi.smul_apply,smul_eq_mul] using
    congrFun (S.chart.repr_comp_embedding_eq_smul x) i

/-- Actual matrix-image membership in a genuine Smith chart. Neither
divisibility nor independent coordinate choices are field-rank claims. -/
theorem exact_membership (x : M) :
    x∈N ↔ (∀ i : Fin n, π^(S.exponent i)∣coord S x (S.chart.f i)) ∧
      (∀ j : I, j∉Set.range S.chart.f → coord S x j=0) := by
  constructor
  · intro hx
    let y : N := ⟨x,hx⟩
    constructor
    · intro i
      change π^(S.exponent i)∣coord S (y:M) (S.chart.f i)
      rw [on_image_coordinate S y i,S.powerDiag,mul_assoc]
      exact dvd_mul_right _ _
    · intro j hj
      exact S.chart.repr_eq_zero_of_notMem_range y hj
  · rintro ⟨hI,hOut⟩
    choose c hc using hI
    let d (i : Fin n) : O := (↑((S.unitCoeff i)⁻¹):O)*c i
    let y : N := S.chart.bN.repr.symm (Finsupp.equivFunOnFinite.symm d)
    have hRep (i : Fin n) : S.chart.bN.repr y i = d i := by simp [y]
    have hEq : S.chart.bM.repr x=S.chart.bM.repr (y:M) := by
      ext j
      change coord S x j = coord S (y:M) j
      by_cases hr : j∈Set.range S.chart.f
      · obtain ⟨i,hi⟩ := hr
        subst j
        rw [hc i,on_image_coordinate S y i,hRep i,S.powerDiag]
        unfold d
        rw [mul_assoc,← mul_assoc (↑(S.unitCoeff i):O),Units.mul_inv,one_mul]
      · rw [hOut j hr]
        exact (S.chart.repr_eq_zero_of_notMem_range y hr).symm
    have hh := S.chart.bM.repr.injective hEq
    rw [hh]
    exact y.property

def realizable (π : O) (L p : ℕ) (N : Submodule O M) (x : M) : Prop :=
  ∃ δ : M, (π^L:O) • (x+(π^p:O) • δ) ∈ N

/-- Necessary and sufficient simultaneous readability in the full module,
before applying the cyclic quotient isomorphism for each active summand. -/
theorem exact_saturation (hπ : π≠0) (L p : ℕ) (x : M) :
    realizable π L p N x ↔
      (∀ i : Fin n, π^(min p (S.exponent i-L))∣coord S x (S.chart.f i)) ∧
      (∀ j : I, j∉Set.range S.chart.f → π^p∣coord S x j) := by
  constructor
  · rintro ⟨δ,hδ⟩
    have h := (exact_membership S _).mp hδ
    constructor
    · intro i
      exact (quotient_modular_dvd O π hπ p (S.exponent i) L _).mp
        ⟨coord S δ (S.chart.f i),by simpa only [coord_scale_add] using h.1 i⟩
    · intro j hj
      have hz := h.2 j hj
      rw [coord_scale_add] at hz
      have hh := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ hπ)
      refine ⟨-coord S δ j,?_⟩
      exact (eq_neg_of_add_eq_zero_left hh).trans (mul_neg _ _).symm
  · rintro ⟨hI,hO⟩
    choose a ha using (fun i : Fin n =>
      (quotient_modular_dvd O π hπ p (S.exponent i) L _).mpr (hI i))
    choose b hb using hO
    let f (j : I) : O :=
      if h : j∈Set.range S.chart.f then a (Classical.choose h) else -b j h
    let δ := fromCoord S f
    have hd (j : I) : coord S δ j=f j := coord_fromCoord S f j
    refine ⟨δ,(exact_membership S _).mpr ⟨?_,?_⟩⟩
    · intro i
      have hm : S.chart.f i∈Set.range S.chart.f := ⟨i,rfl⟩
      have hc : Classical.choose hm=i := S.chart.f.injective (Classical.choose_spec hm)
      rw [coord_scale_add,hd]
      simp only [f,dif_pos hm,hc]
      exact ha i
    · intro j hj
      rw [coord_scale_add,hd]
      simp only [f,dif_neg hj,hb j hj,mul_neg,add_neg_cancel,mul_zero]

#print axioms coord_fromCoord
#print axioms exact_membership
#print axioms exact_saturation
end
end V8CapacitySmith
