import V8CapacityUnifiedMinLoss
import V8CapacityWidthLower

/-! Nonzero factors of U5 in the actual ambient module. The standard
cyclic-coordinate generators can all be used as single target columns. -/
namespace V8CapacityUnified
open scoped Classical BigOperators
open V8CapacityCRTJet V8CapacitySmith V8CapacityWidthUpper V8CapacityGenerator

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000

variable {O X I : Type*} [CommRing O] [IsDomain O] [Fintype X] [Fintype I]
variable {π : O} {E : Submodule O (X → O)} {n : ℕ}
variable (p : ℕ) (S : Powered π E I n) (L : ℕ)

local notation "B" => BaseMod O π p
local notation "Act" => Active S (L+p)

def activeLength (i : Act) : ℕ := p-clipped S L p i.val

theorem activeLength_pos (hp : 0<p) (i : Act) : 0<activeLength p S L i := by
  have hi := i.property
  change S.exponent i.val<L+p at hi
  unfold activeLength clipped
  omega

def activeProj : ((i : Fin n) → BaseMod O π (p-clipped S L p i)) →ₗ[O]
    ((i : Act) → BaseMod O π (activeLength p S L i)) :=
  LinearMap.pi (fun i => LinearMap.proj i.val)

theorem activeProj_bijective : Function.Bijective (activeProj p S L) := by
  constructor
  · intro x y h
    funext i
    by_cases hi : S.exponent i<L+p
    · exact congrFun h ⟨i,hi⟩
    · rw [inactive_module_zero S L p i (Nat.le_of_not_gt hi) (x i),
        inactive_module_zero S L p i (Nat.le_of_not_gt hi) (y i)]
  · intro z
    let f (i : Fin n) : BaseMod O π (p-clipped S L p i) :=
      if hi : S.exponent i<L+p then z ⟨i,hi⟩ else 0
    refine ⟨f,?_⟩
    funext i
    change f i.val=z i
    simp only [f,dif_pos i.property]
    
def activeIso (hπ : π≠0) :
    ((i : Act) → BaseMod O π (activeLength p S L i)) ≃ₗ[O] attainable π L p E :=
  (LinearEquiv.ofBijective (activeProj p S L) (activeProj_bijective p S L)).symm.trans
    ((A4_modules S L p hπ).trans
      (LinearEquiv.ofBijective (U1_to_observed p S hπ L) (U1_to_observed_bijective p S hπ L)).symm)

def activeEmbed (hπ : π≠0) : ((i : Act) → BaseMod O π (activeLength p S L i)) →ₗ[O]
    (X → B) :=
  (attainable π L p E).subtype.comp (activeIso p S L hπ).toLinearMap

theorem activeEmbed_inj (hπ : π≠0) : Function.Injective (activeEmbed p S L hπ) :=
  Subtype.val_injective.comp (activeIso p S L hπ).injective

def generator (hπ : π≠0) (j : Act) : X → B :=
  activeEmbed p S L hπ (fun i => if i=j then 1 else 0)

theorem generator_attains (hπ : π≠0) (j : Act) :
    generator p S L hπ j∈attainable π L p E :=
  ((activeIso p S L hπ) (fun i => if i=j then 1 else 0)).property

theorem generator_sum (hπ : π≠0) (v : X → B) (hv : v∈attainable π L p E) :
    ∃ c : Act → B, v=∑ i : Act, c i • generator p S L hπ i := by
  let w := (activeIso p S L hπ).symm ⟨v,hv⟩
  obtain ⟨a,ha⟩ := coordinate_generates π (activeLength p S L) w
  refine ⟨fun i => coeffMod O π p (a i),?_⟩
  have h := congrArg (activeEmbed p S L hπ) ha
  simp only [map_sum,map_smul] at h
  have h₁ : activeEmbed p S L hπ w=v := by
    change ((activeIso p S L hπ) ((activeIso p S L hπ).symm ⟨v,hv⟩)).val=_
    simp
  rw [h₁] at h
  refine h.trans (Finset.sum_congr rfl (fun i _ => ?_))
  funext x
  rw [Pi.smul_apply,Pi.smul_apply,Algebra.smul_def,smul_eq_mul]
  unfold generator
  apply congrArg (fun z => (coeffMod O π p (a i)) * activeEmbed p S L hπ z x)
  funext j
  by_cases hji : j=i <;> simp [hji]

#print axioms activeLength_pos
#print axioms activeProj_bijective
#print axioms activeIso
#print axioms activeEmbed_inj
#print axioms generator_attains
#print axioms generator_sum
end
end V8CapacityUnified
