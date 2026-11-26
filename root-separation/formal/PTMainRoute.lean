import PTPreprocess
import S6IntegerGate

namespace RootSeparation.Preprocessing

open Finset Filter GraphCutMoments
open scoped BigOperators

def mainT (n : ℕ) : ℕ := (Nat.clog 2 n).sqrt / (Nat.clog 2 (Nat.clog 2 n))^2

theorem mainT_eventually : ∀ᶠ n : ℕ in atTop, 20 ≤ n ∧ 2 ≤ mainT n := by
  open Section6 in
  filter_upwards [eventually_ge_atTop (20:ℕ),
    lambda_atTop.eventually (eventually_rounded 1)] with n hn hr
  have hp : 0 < n := by omega
  have hl := publishedLambda_eq_clog n hp
  have hc : 0 < Nat.clog 2 n := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr
    simpa using (show 1 < n by omega)
  have hnu : publishedNu (publishedLambda n) = Nat.clog 2 (Nat.clog 2 n) := by
    rw [hl]
    exact publishedLambda_eq_clog _ hc
  have hg := hr.groups
  have hnp : 0 < publishedNu (publishedLambda n) := by
    rw [hnu]
    have h1 : 1 < Nat.clog 2 n := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by omega : (2:ℕ)^1 < n)
    exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by simpa using h1)
  rw [publishedRGroups_eq_div _ _ hnp, hnu, hl] at hg
  exact ⟨hn,hg⟩

def gamma (k : ℕ) : ℕ := 4 * ∑ j ∈ range (k-1), 3^j
def mainC (k M : ℕ) : ℕ := 4 * ∑ j ∈ range (k-1), (3*M)^j
def mainB (k M : ℕ) : ℕ := 2 * ∑ j ∈ range k, M^j
def thresholdTest (k t z : ℕ) : Prop :=
  gamma k ≤ 2^z ∧ gamma k * Nat.clog 2 (4 * mainC k (2^z) * 2^z) * t ≤ 2^z

instance (k t z : ℕ) : Decidable (thresholdTest k t z) :=
  inferInstanceAs (Decidable (_ ∧ _))

lemma gamma_four {k : ℕ} (hk : 2 ≤ k) : 4 ≤ gamma k := by
  have h0 : 0 ∈ range (k-1) := mem_range.mpr (by omega)
  have h := single_le_sum (f := fun j : ℕ => (3:ℕ)^j) (fun _ _ => Nat.zero_le _) h0
  norm_num at h
  unfold gamma
  omega

private lemma square_le_twoPow (z : ℕ) (hz : 16 ≤ z) : (z+1)^2 ≤ 2^z := by
  induction z, hz using Nat.le_induction with
  | base => decide
  | succ z hz ih =>
    rw [pow_succ]
    have h : (z+2)^2 ≤ 2*(z+1)^2 := by nlinarith
    exact h.trans (by omega)

private lemma h_upper (k z : ℕ) :
    Nat.clog 2 (4 * mainC k (2^z) * 2^z) ≤ (4+3*k)*(z+1) := by
  let e := (z+2)*k
  have h3 : 3 * (2:ℕ)^z ≤ 2^(z+2) := by
    rw [pow_add]
    have hz : 3 * (2:ℕ)^z ≤ 4 * 2^z := Nat.mul_le_mul_right _ (by decide)
    simpa only [Nat.mul_comm (2^z) (2^2)] using hz
  have hsum : (∑ j ∈ range (k-1), (3*(2:ℕ)^z)^j) ≤ k * 2^e := by
    calc
      _ ≤ ∑ _j ∈ range (k-1), (2:ℕ)^e := by
        apply sum_le_sum
        intro j hj
        rw [mem_range] at hj
        calc
          _ ≤ (2^(z+2):ℕ)^j := Nat.pow_le_pow_left h3 _
          _ ≤ 2^e := by
            rw [← pow_mul]
            exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by omega))
      _ = (k-1)*2^e := by simp
      _ ≤ k*2^e := Nat.mul_le_mul_right _ (by omega)
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  have hk : k ≤ (2:ℕ)^k := Nat.lt_two_pow_self.le
  calc
    _ ≤ 4*(4*(2^k * 2^e))*2^z :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (hsum.trans (Nat.mul_le_mul_right _ hk))))
    _ = 2^(4+k+e+z) := by
      norm_num [pow_add]
      ring
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by decide)
      unfold e
      nlinarith

theorem threshold_exists (k t : ℕ) : ∃ z, thresholdTest k t z := by
  let z := gamma k*t*(4+3*k) + gamma k + 16
  have hz : 16 ≤ z := by unfold z; omega
  have ha : gamma k*t*(4+3*k) ≤ z+1 := by unfold z; omega
  have hb : gamma k ≤ z := by unfold z; omega
  refine ⟨z, hb.trans Nat.lt_two_pow_self.le, ?_⟩
  calc
    _ ≤ gamma k * ((4+3*k)*(z+1)) * t :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (h_upper k z))
    _ = (gamma k*t*(4+3*k))*(z+1) := by ring
    _ ≤ (z+1)^2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ ha
    _ ≤ 2^z := square_le_twoPow _ hz

def thresholdIndex (k t : ℕ) : ℕ := Nat.find (threshold_exists k t)
def mainM (k t : ℕ) : ℕ := 2^(thresholdIndex k t)

theorem threshold_first (k t : ℕ) :
    thresholdTest k t (thresholdIndex k t) ∧
    ∀ z < thresholdIndex k t, ¬ thresholdTest k t z :=
  ⟨Nat.find_spec _, fun _ hz => Nat.find_min _ hz⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

def widthDegree (F : Finset (Finset (Lit V))) (c : ℕ) (H : Finset (Lit V)) : ℕ :=
  (F.filter fun C => C.card = c ∧ H ⊆ C).card

def violation (F : Finset (Finset (Lit V))) (M : ℕ) : Prop :=
  ∃ C ∈ F, ∃ H : Finset (Lit V), H.Nonempty ∧ H ⊂ C ∧ M^(C.card-H.card) ≤ widthDegree F C.card H

private lemma width_two_bound (E : Finset (V × V)) (h : Entry.Simple E) (σ : V → Bool) (l : Lit V) :
    widthDegree (clauseSets (PinnedCNF.formula E σ)) 2 {l} ≤ degree E l.1 := by
  classical
  let Q := E.filter (fun e => e.1 = l.1 ∨ e.2 = l.1)
  let f : V × V → Finset (Lit V) := fun e => {(e.1,true),(e.2,true)}
  have hs : (clauseSets (PinnedCNF.formula E σ)).filter
      (fun C => C.card = 2 ∧ {l} ⊆ C) ⊆ Q.image f := by
    intro C hc
    obtain ⟨hm,hcard,hsub⟩ := mem_filter.mp hc
    obtain ⟨i,rfl⟩ := (mem_clauseSets E σ C).mp hm
    cases i with
    | inl v => simp [clause_card E h σ] at hcard
    | inr e =>
      have hm : l ∈ (Entry.clause E σ (.inr e)).toFinset := hsub (mem_singleton_self _)
      simp only [Entry.clause, List.toFinset_cons, List.toFinset_nil, insert_empty_eq,
        mem_insert, mem_singleton] at hm
      exact mem_image.mpr ⟨e.val, mem_filter.mpr ⟨e.property,hm.imp (fun h => (congrArg Prod.fst h).symm) (fun h => (congrArg Prod.fst h).symm)⟩, by
        simp [f,Entry.clause]⟩
  calc
    _ ≤ (Q.image f).card := card_le_card hs
    _ ≤ Q.card := card_image_le
    _ ≤ _ := by
      unfold Q degree
      rw [filter_or]
      exact card_union_le _ _

theorem normalized_single_leaf (E : Finset (V × V)) (h : Entry.Simple E)
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) {M : ℕ} (hM : 4 ≤ M) :
    ¬ violation (normalized (PinnedCNF.formula E σ)) M := by
  classical
  rw [normalize_pinned E h σ]
  let E' := Entry.survivingEdges E σ
  rintro ⟨C,hC,H,hEmpty,hSub,hDeg⟩
  have hpos := hEmpty.card_pos
  have hlt := card_lt_card hSub
  have cle : C.card ≤ 2 := by
    obtain ⟨i,rfl⟩ := (mem_clauseSets E' σ C).mp hC
    rw [clause_card E' (surviving_simple E h σ) σ]
    cases i <;> simp
  have hc : C.card = 2 := by omega
  have hs : H.card = 1 := by omega
  obtain ⟨l,rfl⟩ := card_eq_one.mp hs
  rw [hc, hs] at hDeg
  simp only [show (2:ℕ)-1=1 by decide, pow_one] at hDeg
  have hh := hDeg.trans ((width_two_bound E' (surviving_simple E h σ) σ l).trans
    ((surviving_degree E σ l.1).trans_eq (reg l.1)))
  omega

def MainLeaf (E : Finset (V × V)) (σ : V → Bool) (k : ℕ) : Prop :=
    let F := normalized (PinnedCNF.formula E σ)
    let t := mainT (Fintype.card V)
    let M := mainM k t
    20 ≤ Fintype.card V ∧ 2 ≤ t ∧
    F.card = Fintype.card V + (Entry.survivingEdges E σ).card ∧
    (∅ : Finset (Lit V)) ∉ F ∧
    1 ≤ F.card ∧
    F.card ≤ mainB k M * Fintype.card V ∧
    thresholdTest k t (thresholdIndex k t) ∧
    (∀ z < thresholdIndex k t, ¬ thresholdTest k t z) ∧
    ¬ violation F M

/-- The normalized input reaches a single sparsifier leaf of the main paper.
The conclusion gives the leaf admission conditions for Counting one sparse formula. -/
theorem main_sparse_leaf (E : Finset (V × V)) (h : Entry.Simple E)
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) {k : ℕ} (hk : 2 ≤ k)
    (hn : 20 ≤ Fintype.card V) (ht : 2 ≤ mainT (Fintype.card V)) : MainLeaf E σ k := by
  unfold MainLeaf
  intro F t M
  have hs := threshold_first k t
  have hM : 4 ≤ M := (gamma_four hk).trans hs.1.1
  have hCard := normalized_clause_count E h σ
  have hB : 5 ≤ mainB k M := by
    have h1 : 1 ∈ range k := mem_range.mpr (by omega)
    have hh := single_le_sum (f := fun j : ℕ => M^j) (fun _ _ => Nat.zero_le _) h1
    simp only [pow_one] at hh
    unfold mainB
    omega
  change F.card = _ at hCard
  refine ⟨hn, ht, hCard, ?_, by omega, ?_, hs.1, hs.2, normalized_single_leaf E h reg σ hM⟩
  · change ∅ ∉ normalized (PinnedCNF.formula E σ)
    rw [normalize_pinned E h σ]
    intro he
    obtain ⟨i,hi⟩ := (mem_clauseSets _ σ _).mp he
    have hh := clause_card _ (surviving_simple E h σ) σ i
    rw [hi,card_empty] at hh
    cases i <;> simp at hh
  · have he := regular_edge_count E 3 reg
    have hle := card_le_card (surviving_subset E σ)
    have hprod := Nat.mul_le_mul_right (Fintype.card V) hB
    change F.card = _ at hCard
    omega

#print axioms mainT_eventually
#print axioms threshold_first
#print axioms normalized_single_leaf
#print axioms main_sparse_leaf


theorem mainT_exact {n x : ℕ} (hn : 20 ≤ n) :
    x ≤ mainT n ↔ x^2 * (Nat.clog 2 (Nat.clog 2 n))^4 ≤ Nat.clog 2 n := by
  let l := Nat.clog 2 n
  let v := Nat.clog 2 l
  have hl : 1 < l := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by omega)
  have hv : 0 < v := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr (by simpa using hl)
  change x ≤ l.sqrt / v^2 ↔ x^2 * v^4 ≤ l
  rw [Nat.le_div_iff_mul_le (pow_pos hv _), Nat.le_sqrt', mul_pow, ← pow_mul]

/-- An explicit polynomial upper bound on the first successful M. The
paper's sharper O(t log t) estimate is not needed for this admission bound. -/
theorem mainM_polynomial (k t : ℕ) :
    mainM k t ≤ 2^18*(gamma k*t*(4+3*k)+gamma k+1)^2 := by
  let A := gamma k*t*(4+3*k)+gamma k+1
  let q := Nat.clog 2 A
  let z := 16+2*q
  have hA : A ≤ 2^q := Nat.le_pow_clog (by decide) A
  have ha : gamma k*t*(4+3*k) ≤ A := by unfold A; omega
  have hg : gamma k ≤ A := by unfold A; omega
  have hj (j : ℕ) : 17+2*j ≤ (2:ℕ)^(j+5) := by
    induction j with
    | zero => decide
    | succ j ih =>
      rw [show j+1+5 = j+5+1 by omega, pow_succ]
      omega
  have hz : z+1 ≤ 2^(q+5) := by have := hj q; unfold z; omega
  have htest : thresholdTest k t z := by
    refine ⟨(hg.trans hA).trans (Nat.pow_le_pow_right (by decide) (by unfold z; omega)),?_⟩
    calc
      _ ≤ gamma k * ((4+3*k)*(z+1)) * t :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (h_upper k z))
      _ = (gamma k*t*(4+3*k))*(z+1) := by ring
      _ ≤ 2^q * 2^(q+5) := Nat.mul_le_mul (ha.trans hA) hz
      _ ≤ 2^z := by
        rw [← pow_add]
        exact Nat.pow_le_pow_right (by decide) (by unfold z; omega)
  have hm : mainM k t ≤ 2^z :=
    Nat.pow_le_pow_right (by decide) (Nat.find_min' _ htest)
  have hi : 2^q ≤ 2*A := by
    by_cases hq : q = 0
    · rw [hq,pow_zero]
      unfold A
      omega
    · have hh : 2^(q-1) < A :=
        (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp (by change q-1 < q; omega)
      have hpow : (2:ℕ)^q = 2^(q-1)*2 := by
        conv_lhs => rw [show q = q-1+1 by omega]
        rw [pow_succ]
      rw [hpow]
      omega
  calc
    _ ≤ 2^z := hm
    _ = 2^16*(2^q)^2 := by unfold z; rw [pow_add, mul_comm 2 q, pow_mul]
    _ ≤ 2^16*(2*A)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hi 2)
    _ = _ := by change _ = 2^18*A^2; ring

theorem mainB_bound (k M : ℕ) (hM : 0 < M) : mainB k M ≤ 2*k*M^(k-1) := by
  unfold mainB
  have h : (∑ j ∈ range k, M^j) ≤ ∑ _j ∈ range k, M^(k-1) := by
    apply sum_le_sum
    intro j hj
    rw [mem_range] at hj
    exact Nat.pow_le_pow_right hM (by omega)
  simpa [mul_assoc] using Nat.mul_le_mul_left 2 h

theorem main_size_threshold : ∃ N0 : ℕ, ∀ N ≥ N0, 20 ≤ N ∧ 2 ≤ mainT N :=
  eventually_atTop.mp mainT_eventually

#print axioms mainT_exact
#print axioms mainM_polynomial
#print axioms mainB_bound
#print axioms main_size_threshold

end RootSeparation.Preprocessing

