import P5SmithExtraction
import P5LiteralCapacity
import Mathlib.Data.Finset.Sort

/-! Complete P2 (A.10) under the manuscript's ordinary DVR assumptions.
An explicit finite permutation orders the elementary exponents, including
zero-length factors and ties. None of the theorems assumes a Smith receipt. -/
namespace Paper5
open scoped BigOperators Polynomial

theorem sortedFinPermutation {s : ℕ} (q : Fin s→ℕ) :
    ∃ e : Fin s ≃ Fin s, Monotone (q ∘ e) := by
  classical
  let code (i : Fin s) : ℕ := (s+1)*q i + i.val
  have hrem (i : Fin s) : code i % (s+1) = i.val := by
    dsimp only [code]
    rw [Nat.mul_add_mod,Nat.mod_eq_of_lt (show i.val<s+1 by have h := i.isLt; omega)]
  have hdiv (i : Fin s) : code i / (s+1) = q i := by
    dsimp only [code]
    rw [Nat.mul_add_div (by omega),Nat.div_eq_of_lt (show i.val<s+1 by have h := i.isLt; omega),Nat.add_zero]
  have hinj : Function.Injective code := by
    intro a b hab
    apply Fin.ext
    exact (hrem a).symm.trans ((congrArg (fun n => n%(s+1)) hab).trans (hrem b))
  let G := Finset.univ.image code
  have hcard : G.card = s := by
    change (Finset.univ.image code).card = _
    rw [Finset.card_image_of_injective (s:=Finset.univ) hinj]
    simp
  let f : Fin s ≃ G := Equiv.ofBijective (fun i => ⟨code i,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩)
    ⟨fun a b hab => hinj (congrArg Subtype.val hab),fun w => by
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp w.property
      exact ⟨i,Subtype.ext hi⟩⟩
  let e := (G.orderIsoOfFin hcard).toEquiv.trans f.symm
  have he (i : Fin s) : code (e i) = (G.orderIsoOfFin hcard i).val := by
    exact congrArg Subtype.val (f.apply_symm_apply (G.orderIsoOfFin hcard i))
  refine ⟨e,fun a b hab => ?_⟩
  change q (e a) ≤ q (e b)
  rw [←hdiv (e a),←hdiv (e b),he,he]
  exact Nat.div_le_div_right ((G.orderIsoOfFin hcard).monotone hab)

variable {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
variable {T : Type*} [Fintype T]

omit [IsLocalRing R] in
theorem literal_observation_sorted_smith {m d : ℕ}
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (t α : T→R) (P k : T→ℕ) (hs : m+d=∑ u,k u) :
    ∃ (lo : Fin m→ℕ) (hi : Fin d→ℕ),
      Monotone lo ∧ Monotone hi ∧ (∀ a b,lo a≤hi b) ∧
      Nonempty (LinearMap.range (scalarObserve π t α P k (∑ u,k u)) ≃ₗ[R]
        CyclicGrid π (Sum.elim lo hi)) := by
  rw [←hs]
  obtain ⟨q,_,⟨S⟩⟩ := literal_observation_has_smith (s:=m+d) π hπ hmax t α P k
  obtain ⟨e,he⟩ := sortedFinPermutation q
  let F : Fin m ⊕ Fin d ≃ Fin (m+d) := finSumFinEquiv
  let a : Fin m → Fin (m+d) := fun i => F (.inl i)
  let b : Fin d → Fin (m+d) := fun i => F (.inr i)
  let lo : Fin m→ℕ := fun i => q (e (a i))
  let hi : Fin d→ℕ := fun i => q (e (b i))
  have hEq : (q ∘ (F.trans e)) = Sum.elim lo hi := by
    funext i
    cases i <;> rfl
  have ha (i : Fin m) : (a i).val = i.val := rfl
  have hb (i : Fin d) : (b i).val = m+i.val := rfl
  have hlo : Monotone lo := by
    intro a₁ a₂ h
    apply he
    change (a a₁).val ≤ (a a₂).val
    simpa only [ha] using h
  have hhi : Monotone hi := by
    intro b₁ b₂ h
    apply he
    change (b b₁).val ≤ (b b₂).val
    simpa only [hb] using Nat.add_le_add_left h m
  have hsep : ∀ i j, lo i≤hi j := by
    intro i j
    apply he
    change (a i).val ≤ (b j).val
    rw [ha,hb]
    have h := i.isLt
    omega
  have e' : CyclicGrid π q ≃ₗ[R] CyclicGrid π (q ∘ (F.trans e)) :=
    (LinearEquiv.piCongrLeft R (fun j => Cyclic π (q j)) (F.trans e)).symm
  rw [hEq] at e'
  exact ⟨lo,hi,hlo,hhi,hsep,⟨S.trans e'⟩⟩

theorem a10_full {N m d : ℕ}
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (t α : T→R) (P k : T→ℕ) (hs : m+d=∑ u,k u)
    (A : Matrix (Fin N) (Fin N) R[X])
    (hdegree : ∀ i j, (A i j).natDegree≤d)
    (hregular : (A.map (Polynomial.mapRingHom (IsLocalRing.residue R))).det≠0) :
    ∃ (lo : Fin m→ℕ) (hi : Fin d→ℕ),
      Monotone lo ∧ Monotone hi ∧ (∀ a b,lo a≤hi b) ∧
      Nonempty (LinearMap.range (scalarObserve π t α P k (∑ u,k u)) ≃ₗ[R]
        CyclicGrid π (Sum.elim lo hi)) ∧
      (N * ∑ a,lo a : ℕ) ≤
        ∑ u, Module.length R (LinearMap.range (localMul A π (t u) (α u) (P u) (k u))) := by
  obtain ⟨lo,hi,hlo,hhi,hsep,⟨S⟩⟩ := literal_observation_sorted_smith π hπ hmax t α P k hs
  exact ⟨lo,hi,hlo,hhi,hsep,⟨S⟩,native_observation_length_scalarSmith π hπ hmax
    t α P k hs A hdegree hregular lo hi hsep S⟩

omit [IsPrincipalIdealRing R] [IsLocalRing R] in
theorem a10_local_channel_budget {N : ℕ}
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (t α : T→R) (P k r : T→ℕ)
    (A : Matrix (Fin N) (Fin N) R[X])
    (g : ∀ u : T, (Fin N→LocalJet π (P u) (k u)) →ₗ[R] (Fin (r u)→LocalJet π (P u) (k u)))
    (h : ∀ u : T, (Fin (r u)→LocalJet π (P u) (k u)) →ₗ[R] (Fin N→LocalJet π (P u) (k u)))
    (fac : ∀ u, localMul A π (t u) (α u) (P u) (k u) = (h u).comp (g u)) :
    ∑ u, Module.length R (LinearMap.range (localMul A π (t u) (α u) (P u) (k u))) ≤
      ∑ u, ((r u * k u * P u : ℕ) : ENat) := by
  exact Finset.sum_le_sum fun u _ => jet_factor_length π hπ hmax _ _ _
    (localMul A π (t u) (α u) (P u) (k u)) (g u) (h u) (fac u)

#print axioms sortedFinPermutation
#print axioms literal_observation_sorted_smith
#print axioms a10_full
#print axioms a10_local_channel_budget
end Paper5
