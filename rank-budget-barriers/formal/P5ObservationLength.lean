import P5PowerMaps

/-! The structural content of v7 (A.10): observers retaining a free
complement lose at most the largest invariant lengths. The proof uses
a scalar-power threshold and actual submodule/quotient length. -/
namespace Paper5
open scoped BigOperators

variable {R : Type*} [CommRing R] [IsDomain R]
variable {I : Type*} [Fintype I]

abbrev CyclicGrid (π : R) (q : I → ℕ) := ((i : I) → Cyclic π (q i))

theorem cyclicGrid_length (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (q : I → ℕ) : Module.length R (CyclicGrid π q) = (∑ i, q i : ℕ) := by
  rw [Module.length_pi_of_fintype]
  simp [cyclic_length π hπ hmax]

/-- For every threshold t: truncate j generators at t, and bound the
remaining pi^t-piece by the actual source's pi^t-piece. -/
theorem generatedQuotient_threshold {Q : Type*} [AddCommGroup Q] [Module R Q]
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (q : I → ℕ) (j t : ℕ)
    (f : CyclicGrid π q →ₗ[R] Q) (hf : Function.Surjective f)
    (g : (Fin j → R) →ₗ[R] Q) (hg : Function.Surjective g) :
    Module.length R Q ≤ (∑ i, (q i-t:ℕ) : ℕ) + (j*t:ℕ) := by
  have h1 := Module.length_le_of_surjective _ (powImageMap_surjective π t f hf)
  have h2 := Module.length_le_of_surjective _ (powQuotMap_surjective π t g hg)
  rw [powerImageCyclicGrid_length π hπ hmax q t] at h1
  rw [powerQuotFree_length (I:=Fin j) π hπ hmax t,Fintype.card_fin] at h2
  rw [length_power_exact (M:=Q) π t]
  exact add_le_add h1 h2

section Split
variable {A : Type*} [AddCommGroup A] [Module R A]
variable (π : R) (q : I → ℕ) (j : ℕ)
variable (obs : (A × (Fin j → R)) →ₗ[R] CyclicGrid π q)

def leftObserved : Submodule R (CyclicGrid π q) :=
  LinearMap.range (obs.comp (LinearMap.inl R A (Fin j→R)))

def retainedComplement : (Fin j→R) →ₗ[R] CyclicGrid π q ⧸ leftObserved π q j obs :=
  (leftObserved π q j obs).mkQ.comp (obs.comp (LinearMap.inr R A (Fin j→R)))

omit [IsDomain R] [Fintype I] in
theorem retainedComplement_surjective (ho : Function.Surjective obs) :
    Function.Surjective (retainedComplement π q j obs) := by
  intro z
  obtain ⟨x,rfl⟩ := Submodule.mkQ_surjective (leftObserved π q j obs) z
  obtain ⟨⟨a,b⟩,rfl⟩ := ho x
  let U := leftObserved π q j obs
  have h0 : U.mkQ (obs (a,0)) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [Submodule.ker_mkQ]
    exact ⟨a,rfl⟩
  have hsum : obs (a,b) = obs (a,0)+obs (0,b) := by
    rw [← map_add]
    congr 1
    simp
  refine ⟨b,?_⟩
  change U.mkQ (obs (0,b)) = U.mkQ (obs (a,b))
  rw [hsum,map_add,h0,zero_add]

theorem sum_exponents (t : ℕ) :
    (∑ i, q i) = (∑ i, min t (q i)) + (∑ i, (q i-t:ℕ)) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by omega)

/-- Lower bound for the actual observed image of the first summand, with
every choice of threshold permitted, including colliding integrally
observed nodes through their invariant exponents. -/
theorem observed_threshold (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (ho : Function.Surjective obs) (t : ℕ) :
    ((∑ i, min t (q i)) - j*t : ℕ) ≤
      Module.length R (leftObserved π q j obs) := by
  let U := leftObserved π q j obs
  let Q := CyclicGrid π q ⧸ U
  have htotal : Module.length R (CyclicGrid π q) =
      Module.length R U + Module.length R Q :=
    Module.length_eq_add_of_exact U.subtype U.mkQ (Submodule.subtype_injective U)
      (Submodule.mkQ_surjective U) (LinearMap.exact_subtype_mkQ U)
  have hsrc := cyclicGrid_length π hπ hmax q
  have hfin : Module.length R (CyclicGrid π q) < ⊤ := hsrc.trans_lt (ENat.coe_lt_top _)
  have hu : Module.length R U ≠ ⊤ :=
    ((Module.length_le_of_injective _ (Submodule.subtype_injective U)).trans_lt hfin).ne
  have hq : Module.length R Q ≠ ⊤ :=
    ((Module.length_le_of_surjective _ (Submodule.mkQ_surjective U)).trans_lt hfin).ne
  have hb := generatedQuotient_threshold π hπ hmax q j t U.mkQ (Submodule.mkQ_surjective U)
    (retainedComplement π q j obs) (retainedComplement_surjective π q j obs ho)
  rw [← Nat.cast_add] at hb
  have hb' := ENat.toNat_le_of_le_coe hb
  change (Module.length R Q).toNat ≤ (∑ i,(q i-t:ℕ)) + j*t at hb'
  have htot := congrArg ENat.toNat (hsrc.symm.trans htotal)
  simp only [ENat.toNat_coe,ENat.toNat_add hu hq] at htot
  have hc : ((∑ i, min t (q i)) - j*t : ℕ) ≤ (Module.length R U).toNat := by
    have he := sum_exponents q t
    omega
  exact (ENat.coe_le_coe.mpr hc).trans_eq (ENat.coe_toNat hu)

/-- A low/high cut separated by threshold t realizes the exact
largest-j removal, even if equal invariant exponents straddle the cut. -/
theorem observed_smallest [DecidableEq I] (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (ho : Function.Surjective obs) (small : Finset I) (t : ℕ)
    (hc : (Finset.univ \ small).card = j)
    (hlo : ∀ i∈small, q i ≤ t) (hhi : ∀ i∈Finset.univ \ small, t ≤ q i) :
    (∑ i∈small, q i : ℕ) ≤ Module.length R (leftObserved π q j obs) := by
  have h1 : (∑ i∈small, min t (q i)) = ∑ i∈small, q i :=
    Finset.sum_congr rfl (fun i hi => min_eq_right (hlo i hi))
  have h2 : (∑ i∈Finset.univ \ small, min t (q i)) = j*t := by
    rw [Finset.sum_congr rfl (fun i hi => min_eq_left (hhi i hi)),Finset.sum_const,hc]
    rfl
  have h3 : (∑ i, min t (q i)) = (∑ i∈small, q i) + j*t := by
    rw [← Finset.sum_sdiff (Finset.subset_univ small),h1,h2,add_comm]
  have hb := observed_threshold π q j obs hπ hmax ho t
  rw [h3,Nat.add_sub_cancel] at hb
  exact hb
end Split

#print axioms cyclicGrid_length
#print axioms generatedQuotient_threshold
#print axioms retainedComplement_surjective
#print axioms observed_threshold
#print axioms observed_smallest
end Paper5
