import P5ObservationLength

/-! Repeating the invariant-length list N times, as in (A.10), and
the actual finite local-channel upper bound. The module accepts a split
of the observation domain and the literal local images; extraction of
that split from a primitive polynomial-multiplication matrix is a
separate source theorem, not hidden in the statement. -/
namespace Paper5
open scoped BigOperators

variable {R : Type*} [CommRing R] [IsDomain R]

abbrev RepIndex (N m j : ℕ) := (Fin N × Fin m) ⊕ (Fin N × Fin j)

def repExponent {N m j : ℕ} (low : Fin m → ℕ) (high : Fin j → ℕ) : RepIndex N m j → ℕ
  | .inl i => low i.2
  | .inr i => high i.2

def smallSide (N m j : ℕ) : Finset (RepIndex N m j) :=
  Finset.univ.map ⟨Sum.inl,Sum.inl_injective⟩

def largeSide (N m j : ℕ) : Finset (RepIndex N m j) :=
  Finset.univ.map ⟨Sum.inr,Sum.inr_injective⟩

theorem complement_small (N m j : ℕ) :
    Finset.univ \ smallSide N m j = largeSide N m j := by
  ext i
  cases i <;> simp [smallSide,largeSide]

theorem card_large (N m j : ℕ) : (largeSide N m j).card = j*N := by
  simp [largeSide,Nat.mul_comm]

theorem sum_small {N m j : ℕ} (lo : Fin m → ℕ) (hi : Fin j → ℕ) :
    (∑ i∈smallSide N m j, repExponent lo hi i) = N * ∑ a, lo a := by
  simp [smallSide,repExponent,Fintype.sum_prod_type]

theorem threshold_of_cut {m j : ℕ} (lo : Fin m → ℕ) (hi : Fin j → ℕ)
    (h : ∀ i k, lo i ≤ hi k) : ∃ t, (∀ i, lo i≤t) ∧ (∀ k, t≤hi k) :=
  ⟨Finset.univ.sup lo,fun i => Finset.le_sup (Finset.mem_univ i),
    fun k => Finset.sup_le fun i _ => h i k⟩

section Rep
variable {N m j : ℕ} {W : Type*} [AddCommGroup W] [Module R W]
variable (π : R)
variable (lo : Fin m → ℕ) (hi : Fin j → ℕ)
variable (obs : (W × (Fin (j*N) → R)) →ₗ[R] CyclicGrid π (repExponent lo hi : RepIndex N m j → ℕ))

theorem repeated_observed (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (ho : Function.Surjective obs) (hsep : ∀ i k, lo i ≤ hi k) :
    (N * ∑ i, lo i : ℕ) ≤ Module.length R (leftObserved π (repExponent lo hi) (j*N) obs) := by
  obtain ⟨t,hlo,hhi⟩ := threshold_of_cut lo hi hsep
  have hc : (Finset.univ \ smallSide N m j).card = j*N := by
    rw [complement_small,card_large]
  have hs i (h : i∈smallSide N m j) : repExponent lo hi i ≤ t := by
    obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp h
    exact hlo x.2
  have hl i (h : i∈Finset.univ \ smallSide N m j) : t ≤ repExponent lo hi i := by
    rw [complement_small] at h
    obtain ⟨x,_,rfl⟩ := Finset.mem_map.mp h
    exact hhi x.2
  have h := observed_smallest π (repExponent lo hi) (j*N) obs hπ hmax ho
    (smallSide N m j) t hc hs hl
  rw [sum_small] at h
  exact h

variable {T : Type*} [Fintype T] {V : T → Type*}
  [∀ t, AddCommGroup (V t)] [∀ t, Module R (V t)]

/-- The left observed image has a checked injection into the product
of the stated local images, constructed from the source embedding. -/
noncomputable def observeIntoLocal
    (embed : CyclicGrid π (repExponent lo hi : RepIndex N m j → ℕ) →ₗ[R] (∀ t, V t))
    (L : ∀ t, Submodule R (V t))
    (hit : ∀ w t, embed (obs (w,0)) t ∈ L t) :
    leftObserved π (repExponent lo hi) (j*N) obs →ₗ[R] ∀ t, L t :=
  LinearMap.pi fun t =>
    ((LinearMap.proj t).comp (embed.comp (leftObserved π (repExponent lo hi) (j*N) obs).subtype)).codRestrict
      (L t) (fun x => by
        obtain ⟨w,hw⟩ := x.property
        change obs (w,0) = x.val at hw
        change embed x.val t ∈ L t
        rw [←hw]
        exact hit w t)

omit [IsDomain R] [Fintype T] in
theorem observeIntoLocal_injective
    (embed : CyclicGrid π (repExponent lo hi : RepIndex N m j → ℕ) →ₗ[R] (∀ t, V t))
    (he : Function.Injective embed) (L : ∀ t, Submodule R (V t))
    (hit : ∀ w t, embed (obs (w,0)) t ∈ L t) :
    Function.Injective (observeIntoLocal π lo hi obs embed L hit) := by
  intro x y h
  apply Subtype.ext
  apply he
  funext t
  exact congrArg (fun f : ∀ t, L t => (f t : V t)) h

/-- Observation-length inequality (A.10), once the source multiplication
domain is split and its observation image is identified with its Smith
list. No residue-distinctness is assumed. -/
theorem observation_length_lower (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (ho : Function.Surjective obs) (hsep : ∀ i k, lo i ≤ hi k)
    (embed : CyclicGrid π (repExponent lo hi : RepIndex N m j → ℕ) →ₗ[R] (∀ t, V t))
    (he : Function.Injective embed) (L : ∀ t, Submodule R (V t))
    (hit : ∀ w t, embed (obs (w,0)) t ∈ L t) :
    (N * ∑ i, lo i : ℕ) ≤ ∑ t, Module.length R (L t) := by
  have hl := repeated_observed π lo hi obs hπ hmax ho hsep
  have hu := Module.length_le_of_injective _ (observeIntoLocal_injective π lo hi obs embed he L hit)
  rw [Module.length_pi_of_fintype] at hu
  exact hl.trans hu
end Rep

/-- Local data are an actual image in a module. A factorization through
r channel jets, each with k coefficients in R/(pi^P), bounds its length
by r*k*P, rather than treating the ring as its residue field. -/
theorem local_channel_length {Z : Type*} [AddCommGroup Z] [Module R Z]
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (r k P : ℕ) (F : (Fin r × Fin k → Cyclic π P) →ₗ[R] Z)
    (L : Submodule R Z) (h : L ≤ LinearMap.range F) :
    Module.length R L ≤ (r*k*P:ℕ) := by
  have ha := Module.length_le_of_injective (Submodule.inclusion h) (Submodule.inclusion_injective h)
  have hs : Function.Surjective F.rangeRestrict := by
    intro y
    obtain ⟨x,hx⟩ := y.property
    exact ⟨x,Subtype.ext hx⟩
  have hb := Module.length_le_of_surjective F.rangeRestrict hs
  have hc : Module.length R (Fin r × Fin k → Cyclic π P) = (r*k*P:ℕ) := by
    simpa using cyclicGrid_length π hπ hmax (fun _ : Fin r × Fin k => P)
  exact ha.trans (hb.trans_eq hc)

#print axioms complement_small
#print axioms card_large
#print axioms sum_small
#print axioms threshold_of_cut
#print axioms repeated_observed
#print axioms observeIntoLocal_injective
#print axioms observation_length_lower
#print axioms local_channel_length
end Paper5
