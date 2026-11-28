import V8CapacityWidthUpper
import V8CapacityWidthLower

/-! Realized integral columns for all active Smith directions. A single
finite set of generator columns suffices for the width lower bound. -/
namespace V8CapacityActiveWitness
open scoped Classical BigOperators
open V8CapacityCRTJet V8CapacityCyclic V8CapacityGenerator V8CapacitySmith
open V8CapacityWidthUpper V8CapacityWidthLower

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {O M I : Type*} [CommRing O] [IsDomain O]
variable [AddCommGroup M] [Module O M] [Fintype I]
variable {π : O} {N : Submodule O M} {n : ℕ}
variable (S : Powered π N I n) (hπ : π≠0) (L p : ℕ)

variable {F : Type*} [Fintype F]

abbrev Index (S : Powered π N I n) (L p : ℕ) (F : Type*) := F × Active S (L+p)

def length (i : Index S L p F) : ℕ :=
  p-clipped S L p i.2

def embed : ((i : Index S L p F) → BaseMod O π (length S L p i)) →ₗ[O]
    (Index S L p F → BaseMod O π p) :=
  LinearMap.pi fun i =>
    (component S L p i.2).subtype.comp
      ((cyclicIso O π hπ p (clipped S L p i.2) (min_le_left _ _)).toLinearMap.comp
        (LinearMap.proj i))

theorem embed_apply (x : (i : Index S L p F) → BaseMod O π (length S L p i))
    (i : Index S L p F) :
    embed S hπ L p x i =
      ((cyclicIso O π hπ p (clipped S L p i.2) (min_le_left _ _) (x i) : component S L p i.2)
        : BaseMod O π p) := rfl

theorem embed_inj : Function.Injective (embed S hπ L p (F:=F)) := by
  intro x y h
  funext i
  have hx := congrFun h i
  rw [embed_apply,embed_apply] at hx
  exact (cyclicIso O π hπ p (clipped S L p i.2) (min_le_left _ _)).injective (Subtype.ext hx)

theorem positive_length (hp : 0<p) (i : Index S L p F) : 0<length S L p i := by
  have hi := i.2.property
  change S.exponent i.2.val<L+p at hi
  simp only [length,clipped]
  omega

/-- Every vector in the product of active cyclic quotients is an
observable column, independently on all fibers. No promise of cheaper
realization or field-level independence is used. -/
theorem embed_realizable (w : (i : Index S L p F) → BaseMod O π (length S L p i)) :
    ∃ x : F → M, (∀ f, realizable π L p N (x f)) ∧
      ∀ i : Index S L p F,
      coeffMod O π p (coord S (x i.1) (S.chart.f i.2))=embed S hπ L p w i := by
  let z (f : F) (i : Fin n) : BaseMod O π p :=
    if h : S.exponent i<L+p then embed S hπ L p w (f,⟨i,h⟩) else 0
  have hz (f : F) : z f∈observed S L p := by
    apply Submodule.mem_pi.mpr
    intro i _
    unfold z
    split_ifs with hi
    · rw [embed_apply]
      exact (cyclicIso O π hπ p (clipped S L p i) (min_le_left _ _) (w (f,⟨i,hi⟩))).property
    · exact zero_mem _
  choose x hx hread using (fun f : F => (readable_obs S L p hπ (z f)).mp (hz f))
  refine ⟨x,hx,?_⟩
  intro i
  simpa only [z,dif_pos i.2.property] using hread i.1 i.2

variable [IsLocalRing O] [IsPrincipalIdealRing O]
variable {Rows J : Type*} [Fintype J]

def basisDigit (i : Index S L p F) (j : Index S L p F) :
    BaseMod O π (length S L p j) :=
  if j=i then 1 else 0

/-- A matrix carrying columns that recover the active coordinate
generators cannot factor through fewer R_p coordinates. This is the
executable A3 witness criterion, not an assumption that the arbitrary
factorization factors through the actual Smith image. -/
theorem witness_requires_width (hp : 0<p) (hz : IsLocalRing.residue O π=0)
    (receive : (Rows → BaseMod O π p) →ₗ[BaseMod O π p] (Index S L p F → BaseMod O π p))
    (out : Index S L p F → (Rows → BaseMod O π p))
    (hgen : ∀ i, receive (out i)=embed S hπ L p (basisDigit S L p i))
    (fac : (J → BaseMod O π p) →ₗ[BaseMod O π p] (Rows → BaseMod O π p))
    (hfac : ∀ i, ∃ z, fac z=out i) :
    Fintype.card (Index S L p F)≤Fintype.card J := by
  choose z hz' using hfac
  apply residue_embedded_cyclic_width π hz (length S L p) (positive_length S L p hp) p
    (embed S hπ L p (F:=F)) (embed_inj S hπ L p) (receive.comp fac)
  intro w
  obtain ⟨a,ha⟩ := coordinate_generates π (length S L p (F:=F)) w
  refine ⟨∑ i : Index S L p F, coeffMod O π p (a i) • z i,?_⟩
  rw [ha,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,map_smul,LinearMap.comp_apply,hz' i,hgen i]
  funext j
  rw [Pi.smul_apply,Pi.smul_apply,smul_eq_mul,Algebra.smul_def]
  rw [show (algebraMap O (BaseMod O π p)) (a i)=coeffMod O π p (a i) by rfl]
  have hd : basisDigit S L p i = (fun t : Index S L p F =>
      if t=i then (1:BaseMod O π (length S L p t)) else 0) := by
    funext t
    unfold basisDigit
    by_cases h : t=i
    · simp [h]
    · simp [h]
  rw [hd]
  simp only [embed_apply]
  by_cases h : j=i
  · simp [h]
  · simp [h]

#print axioms embed_apply
#print axioms embed_inj
#print axioms positive_length
#print axioms embed_realizable
#print axioms witness_requires_width
end
end V8CapacityActiveWitness

