import V8CapacitySpecialSplit

/-! A basis-free numerical valuation profile: the residue dimension of
the pi^b-saturation layer equals the number of exponents ≤ b. This
recovers the entire multiset, not only the number below precision P. -/
namespace V8CapacitySpecialProfile
open scoped Classical BigOperators
open V8CapacitySpecialSplit Module

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1150000

variable {O I J T : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [Fintype I] [Fintype J] [Fintype T]
variable {π : O} {N : Submodule O (I → O)}

local notation "κ" => IsLocalRing.ResidueField O

def red {T : Type*} (z : T → O) : T → κ := fun i => IsLocalRing.residue O (z i)

def std (j : J) : J → O := Pi.single j 1

def resGen (S : Split π N J) (j : J) : I → κ :=
  red (S.embed (std j))

def saturation (π : O) (b : ℕ) (N : Submodule O (I → O)) : Submodule O (I → O) :=
  N.comap ((π^b:O) • LinearMap.id)

def satSpan (π : O) (b : ℕ) (N : Submodule O (I → O)) : Submodule κ (I → κ) :=
  Submodule.span κ (Set.range (fun x : saturation π b N => red x.val))

theorem expansion_std (w : J → O) : (∑ j : J, w j • std j)=w := by
  funext i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp [std]
  · intro j _ h
    simp [std,Ne.symm h]

theorem reduction_combination (S : Split π N J) (w : J → O) :
    red (S.embed w)=∑ j : J, IsLocalRing.residue O (w j) • resGen S j := by
  conv_lhs => rw [← expansion_std w,map_sum]
  funext i
  simp only [red,resGen,Finset.sum_apply,map_sum,map_smul,Pi.smul_apply,smul_eq_mul,map_mul]
 
theorem full_reduced_independent (S : Split π N J) : LinearIndependent κ (resGen S) := by
  let A : Matrix J I O := LinearMap.toMatrix' S.proj
  let Q : Matrix J I κ := A.map (IsLocalRing.residue O)
  apply LinearIndependent.of_comp Q.mulVecLin
  have h (j : J) : Q.mulVecLin (resGen S j)=Pi.basisFun κ J j := by
    funext i
    change (A.map (IsLocalRing.residue O)).mulVec
      ((IsLocalRing.residue O) ∘ S.embed (std j)) i = _
    rw [← RingHom.map_mulVec,LinearMap.toMatrix'_mulVec,S.left,Pi.basisFun_apply]
    by_cases hi : i=j
    · subst i
      simp [std]
    · simp [std,hi]
  have hh : (Q.mulVecLin ∘ resGen S) = Pi.basisFun κ J := funext h
  rw [hh]
  exact (Pi.basisFun κ J).linearIndependent

theorem sat_span_description (S : Split π N J) (hπ : π≠0)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O)) (b : ℕ) :
    satSpan π b N=Submodule.span κ (Set.range (fun j : {j // S.exp j≤b} => resGen S j.val)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x,rfl⟩
    have h := (sat_iff S hπ b x.val).mp x.property
    have he : red x.val=∑ j : J, IsLocalRing.residue O (S.proj x.val j) • resGen S j :=
      (congrArg red h.1.symm).trans (reduction_combination S _)
    change red x.val ∈ _
    rw [he]
    apply Submodule.sum_mem
    intro j _
    by_cases hj : S.exp j≤b
    · apply Submodule.smul_mem
      exact Submodule.subset_span ⟨⟨j,hj⟩,rfl⟩
    · have hd : π∣S.proj x.val j := by
        have hlt : 1≤S.exp j-b := by omega
        exact ((show π∣π^(S.exp j-b) by simpa only [pow_one] using
          (pow_dvd_pow π hlt))).trans (h.2 j)
      have hz : IsLocalRing.residue O (S.proj x.val j)=0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr (by rwa [hMax,Ideal.mem_span_singleton])
      rw [hz,zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    apply Submodule.subset_span
    have hp : (π^b:O) • S.embed (std j.val)∈N := by
      apply (sat_iff S hπ b _).mpr
      rw [S.left]
      refine ⟨rfl,?_⟩
      intro i
      by_cases he : i=j.val
      · subst i
        rw [Nat.sub_eq_zero_of_le j.property,pow_zero]
        exact one_dvd _
      · have hz : (std j.val : J→O) i=0 := by simp [std,he]
        rw [hz]
        exact dvd_zero _
    exact ⟨⟨S.embed (std j.val),hp⟩,rfl⟩

theorem profile_card (S : Split π N J) (hπ : π≠0)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O)) (b : ℕ) :
    Module.finrank κ (satSpan π b N)=Fintype.card {j // S.exp j≤b} := by
  rw [sat_span_description S hπ hMax b]
  have h := (full_reduced_independent S).comp (Subtype.val : {j // S.exp j≤b}→J)
    Subtype.val_injective
  exact finrank_span_eq_card h

theorem same_exponent_profile (S : Split π N J) (T₀ : Split π N T) (hπ : π≠0)
    (hMax : IsLocalRing.maximalIdeal O=Ideal.span ({π}:Set O)) (b : ℕ) :
    Fintype.card {j // S.exp j≤b}=Fintype.card {j // T₀.exp j≤b} :=
  (profile_card S hπ hMax b).symm.trans (profile_card T₀ hπ hMax b)

#print axioms expansion_std
#print axioms reduction_combination
#print axioms full_reduced_independent
#print axioms sat_span_description
#print axioms profile_card
#print axioms same_exponent_profile
end
end V8CapacitySpecialProfile

