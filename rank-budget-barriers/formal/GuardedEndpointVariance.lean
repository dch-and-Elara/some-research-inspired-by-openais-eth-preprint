import PacketVariance
import RandomEndpoint

/-! P11 independent whole-type randomness and the physical endpoint
sensitivity argument. For any old equality, each of its actual ports has
that equality as owner. The local sample space and the endpoint expectation
can be supplied separately, e.g. by the proved cell-probability lemma. -/

namespace GuardedEndpointVariance
open scoped BigOperators
open PacketVariance
noncomputable section

variable {n : ℕ} {T : Fin n → Type*} {Port Eq : Type*}
  [DecidableEq Port] [DecidableEq Eq] [Fintype Eq]

def picked (S : ∀ i, T i → Finset Port) (a : ∀ i, T i) : Finset Port :=
  Finset.univ.biUnion fun i => S i (a i)

def guarded (legs : Eq → Finset Port) (s : Finset Port) : Finset Eq :=
  Finset.univ.filter fun e => legs e ⊆ s

def count (S : ∀ i, T i → Finset Port) (legs : Eq → Finset Port)
    (a : ∀ i, T i) : ℚ :=
  (guarded legs (picked S a)).card

theorem newlyGuarded (S : ∀ i, T i → Finset Port)
    (legs : Eq → Finset Port) (owner : Port → Eq)
    (owns : ∀ e p, p ∈ legs e → owner p = e)
    (j : Fin n) (a b : ∀ i, T i) (h : ∀ i, i ≠ j → a i = b i) :
    guarded legs (picked S a) ⊆ guarded legs (picked S b) ∪ (S j (a j)).image owner := by
  classical
  intro e he
  apply Finset.mem_union.mpr
  by_cases hb : e ∈ guarded legs (picked S b)
  · exact Or.inl hb
  · right
    have hna : ¬ legs e ⊆ picked S b := by simpa [guarded] using hb
    obtain ⟨p,hp,hpn⟩ := Finset.not_subset.mp hna
    have ha : legs e ⊆ picked S a := (Finset.mem_filter.mp he).2
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp (ha hp)
    have eij : i = j := by
      by_contra hn
      apply hpn
      rw [h i hn] at hi
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩
    subst i
    exact Finset.mem_image.mpr ⟨p,hi,owns e p hp⟩

/-- Sharper than twice the packet count: use a newly occupied port for
an increase and a lost port for a decrease, never their sum. -/
theorem changedAtMost (S : ∀ i, T i → Finset Port)
    (legs : Eq → Finset Port) (owner : Port → Eq)
    (owns : ∀ e p, p ∈ legs e → owner p = e) (P : Fin n → ℕ)
    (cap : ∀ i a, (S i a).card ≤ P i) :
    sensitive (count S legs) (fun j => (P j : ℚ)) := by
  intro j a b hagree
  have hle (x y : ∀ i, T i) (hxy : ∀ i, i ≠ j → x i = y i) :
      (guarded legs (picked S x)).card ≤ (guarded legs (picked S y)).card + P j :=
    (Finset.card_le_card (newlyGuarded S legs owner owns j x y hxy)).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_left
        ((Finset.card_image_le).trans (cap j (x j))) _))
  have h₁ : count S legs a ≤ count S legs b + (P j : ℚ) := by
    unfold count
    exact_mod_cast hle a b hagree
  have h₂ : count S legs b ≤ count S legs a + (P j : ℚ) := by
    unfold count
    exact_mod_cast hle b a (fun i hi => (hagree i hi).symm)
  rw [abs_le]
  constructor <;> linarith

variable [∀ i, Fintype (T i)] [∀ i, Nonempty (T i)]

theorem physical_variance (S : ∀ i, T i → Finset Port)
    (legs : Eq → Finset Port) (owner : Port → Eq)
    (owns : ∀ e p, p ∈ legs e → owner p = e)
    (w : ∀ i, T i → ℚ) (P : Fin n → ℕ) (H : ℕ)
    (hw : ∀ i, prob (w i)) (hP : ∀ i, P i ≤ H)
    (cap : ∀ i a, (S i a).card ≤ P i) :
    variance (product w) (count S legs) ≤ H * ∑ i, (P i : ℚ) := by
  refine (bounded_differences w _ _ hw (changedAtMost S legs owner owns P cap)).trans ?_
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h : (P i : ℚ) ≤ H := by exact_mod_cast hP i
  simpa [pow_two] using mul_le_mul_of_nonneg_right h (show (0:ℚ) ≤ P i by positivity)

/-- Both endpoints obey P11's original Chebyshev estimate with the
variance premise discharged from whole-type independence. The expectation
bounds are established separately from exact within-cell sampling. -/
theorem endpoint_tail (left right : ∀ i, T i → Finset Port)
    (legs : Eq → Finset Port) (owner : Port → Eq)
    (owns : ∀ e p, p ∈ legs e → owner p = e)
    (w : ∀ i, T i → ℚ) (P : Fin n → ℕ) (H : ℕ)
    (hw : ∀ i, prob (w i)) (hP : ∀ i, P i ≤ H)
    (cl : ∀ i a, (left i a).card ≤ P i) (cr : ∀ i a, (right i a).card ≤ P i)
    (L M D b : ℚ) (hL : 0 < L) (hM : 0 < M) (hD : 0 < D)
    (hpack : (∑ i, (P i : ℚ))*L = H*D)
    (hbound : (∑ i, (P i : ℚ))*L ≤ 2*M)
    (hleft : (1-1/b)*(M/(2*L^2)) ≤ avg (product w) (count left legs))
    (hright : (1-1/b)*(M/(2*L^2)) ≤ avg (product w) (count right legs)) :
    1-128*L^7/D ≤ RandomEndpoint.probability (product w) (fun a =>
      (1-1/b-1/L^2)*(M/(2*L^2)) ≤ count left legs a ∧
      (1-1/b-1/L^2)*(M/(2*L^2)) ≤ count right legs a) := by
  classical
  have hnon (a : ∀ i, T i) : 0 ≤ product w a :=
    Finset.prod_nonneg (fun i _ => (hw i).1 (a i))
  have hnorm : (∑ a, product w a) = 1 := by
    unfold product
    rw [← Fintype.prod_sum]
    apply Finset.prod_eq_one
    intro i _
    exact (hw i).2
  have HP : (H:ℚ)*(∑ i, (P i : ℚ)) ≤ 4*H*(∑ i, (P i : ℚ)) := by
    have q : 0 ≤ (H:ℚ)*(∑ i, (P i : ℚ)) := by positivity
    linarith
  have bound := RandomEndpoint.relative_variance_bound H (∑ i, (P i : ℚ)) L M D
    (by positivity) hL hD hpack hbound
  refine RandomEndpoint.native_tail_from_moments (product w) (count left legs)
    (count right legs) (avg (product w) (count left legs)) (avg (product w) (count right legs))
    (M/(2*L^2)) L D b (by positivity) hL hD hnon hnorm hleft hright ?_ ?_
  · exact (physical_variance left legs owner owns w P H hw hP cl).trans (HP.trans bound)
  · exact (physical_variance right legs owner owns w P H hw hP cr).trans (HP.trans bound)

#print axioms endpoint_tail
#print axioms newlyGuarded
#print axioms changedAtMost
#print axioms physical_variance
end
end GuardedEndpointVariance