import P5NativeEntryHash

/-! Greedy full enumeration in source lines 3483–3529.  Every minimizer,
not just a favorable tie, raises rank until it is full. -/
namespace Paper5.NativeEntry
open scoped BigOperators

def support {n : ℕ} (r : Word n) : Finset (Fin n) :=
  Finset.univ.filter fun v=>r v≠0

@[simp] theorem mem_support {n : ℕ} (r : Word n) (v : Fin n) :
    v∈support r ↔ r v≠0 := by simp [support]

theorem candidate_width {n P : ℕ} (γ : Candidate n P) :
    (support (candidateRow γ)).card≤P := by
  calc
    _ ≤ (Finset.univ.image fun j : Fin P=>(γ j).1).card := by
      apply Finset.card_le_card
      intro v hv
      by_contra hnv
      have h : ∀ j, (γ j).1≠v := by simpa using hnv
      simp [mem_support,candidateRow,h] at hv
    _ ≤ (Finset.univ : Finset (Fin P)).card := Finset.card_image_le
    _ = P := by simp

theorem min_count_one_step {n P : ℕ} (sgn : Fin n → Bool) (A : Rows n)
    (hP : 0<P) (γ : Candidate n P)
    (hMin : ∀ δ : Candidate n P,
      acceptedCount (A++[candidateRow γ]) sgn ≤ acceptedCount (A++[candidateRow δ]) sgn) :
    nullity (A++[candidateRow γ])=nullity A-1 := by
  have hLoHi := nullity_append_bounds A (candidateRow γ)
  by_cases h : 0<nullity A
  · obtain ⟨v,hv⟩ := some_singleton_progress A h
    have hh := hMin (singletonList hP v)
    simp only [singleton_represented,accepted_count_exact] at hh
    have hh' : nullity (A++[candidateRow γ]) ≤ nullity (A++[singletonRow v]) :=
      (Nat.pow_le_pow_iff_right (by decide : 1<(2:ℕ))).mp hh
    omega
  · omega

theorem exists_minimizer {n P : ℕ} (hn : 0<n) (sgn : Fin n → Bool) (A : Rows n) :
    ∃ γ : Candidate n P, ∀ δ : Candidate n P,
      acceptedCount (A++[candidateRow γ]) sgn≤acceptedCount (A++[candidateRow δ]) sgn := by
  classical
  let γ₀ : Candidate n P := fun _=>(⟨0,hn⟩,0)
  obtain ⟨γ,_,h⟩ := Finset.exists_min_image (Finset.univ : Finset (Candidate n P))
    (fun γ=>acceptedCount (A++[candidateRow γ]) sgn) ⟨γ₀,Finset.mem_univ _⟩
  exact ⟨γ,fun δ=>h δ (Finset.mem_univ _)⟩

/-- The data-independent order of the source is allowed to resolve ties
arbitrarily; the theorem applies to all such executions. -/
structure Greedy {n P : ℕ} (sgn : Fin n → Bool) (A₀ : Rows n) where
  rows : ℕ → Rows n
  chosen : ℕ → Candidate n P
  start : rows 0=A₀
  step : ∀ j<3*n,rows (j+1)=rows j++[candidateRow (chosen j)]
  minimal : ∀ j<3*n,∀ γ : Candidate n P,
    acceptedCount (rows j++[candidateRow (chosen j)]) sgn ≤
      acceptedCount (rows j++[candidateRow γ]) sgn

theorem greedy_nullity {n P : ℕ} {sgn : Fin n → Bool} {A₀ : Rows n}
    (run : @Greedy n P sgn A₀) (hP : 0<P) (j : ℕ) (hj : j≤3*n) :
    nullity (run.rows j)=nullity A₀-j := by
  induction j with
  | zero => simp [run.start]
  | succ j ih =>
    have h := min_count_one_step sgn (run.rows j) hP (run.chosen j)
      (run.minimal j (by omega))
    rw [run.step j (by omega),h,ih (by omega)]
    omega

theorem greedy_full_rank {n P : ℕ} {sgn : Fin n → Bool} {A₀ : Rows n}
    (run : @Greedy n P sgn A₀) (hP : 0<P) (j : ℕ) (hj : n≤j) (hJ : j≤3*n) :
    (matrix (run.rows j)).rank=n := by
  have hd := rank_add_nullity A₀
  have hp := rank_add_nullity (run.rows j)
  rw [greedy_nullity run hP j hJ] at hp
  omega

theorem first_full_rank_query_reached {n P : ℕ} {sgn : Fin n → Bool} {A₀ : Rows n}
    (run : @Greedy n P sgn A₀) (hP : 0<P) (hn : 0<n) :
    ∃ j<3*n, ∃ γ : Candidate n P, (matrix (run.rows j++[candidateRow γ])).rank=n := by
  refine ⟨n-1,by omega,run.chosen (n-1),?_⟩
  rw [←run.step (n-1) (by omega),show n-1+1=n by omega]
  exact greedy_full_rank run hP n le_rfl (by omega)

theorem greedy_length {n P : ℕ} {sgn : Fin n → Bool} {A₀ : Rows n}
    (run : @Greedy n P sgn A₀) (j : ℕ) (hj : j≤3*n) :
    (run.rows j).length=A₀.length+j := by
  induction j with
  | zero => simp [run.start]
  | succ j ih => rw [run.step j (by omega)]; simp [ih (by omega),Nat.add_assoc]

theorem greedy_width {n P W : ℕ} {sgn : Fin n → Bool} {A₀ : Rows n}
    (run : @Greedy n P sgn A₀) (j : ℕ) (hj : j≤3*n) (hP : P≤W)
    (hA : ∀ r∈A₀,(support r).card≤W) :
    ∀ r∈run.rows j,(support r).card≤W := by
  induction j with
  | zero => rwa [run.start]
  | succ j ih =>
    intro r hr
    rw [run.step j (by omega),List.mem_append,List.mem_singleton] at hr
    rcases hr with h|rfl
    · exact ih (by omega) _ h
    · exact (candidate_width _).trans hP

def hashMu (n : ℕ) : ℕ := Nat.log 2 n+1
def hashP (n B : ℕ) : ℕ := 20000*B^2*(hashMu n)^2
def hashD₀ (n B : ℕ) : ℕ := 320000*B^2*(hashMu n)^3

theorem actual_params {n B : ℕ} (hB : 0<B) :
    0<hashP n B ∧ hashP n B≤hashD₀ n B := by
  have hm : 1≤hashMu n := by simp [hashMu]
  have he : (hashMu n)^2≤(hashMu n)^3 :=
    Nat.pow_le_pow_right (by omega) (by omega)
  exact ⟨by unfold hashP; positivity,
    Nat.mul_le_mul (Nat.mul_le_mul_right (B^2) (show (20000:ℕ)≤320000 by decide)) he⟩

theorem final_source_rank_width {n B : ℕ} {sgn : Fin n → Bool} {A₀ : Rows n}
    (run : @Greedy n (hashP n B) sgn A₀) (hB : 0<B)
    (hInit : A₀.length≤3*n) (hWidths : ∀ r∈A₀,(support r).card≤hashD₀ n B) :
    (matrix (run.rows (3*n))).rank=n ∧ (run.rows (3*n)).length≤6*n ∧
      (∀ r∈run.rows (3*n),(support r).card≤hashD₀ n B) := by
  have ⟨hP,hPD⟩ := actual_params (n:=n) hB
  refine ⟨greedy_full_rank run hP (3*n) (by omega) le_rfl,?_,
    greedy_width run _ le_rfl hPD hWidths⟩
  rw [greedy_length run (3*n) le_rfl]
  omega

#print axioms candidate_width
#print axioms exists_minimizer
#print axioms min_count_one_step
#print axioms greedy_nullity
#print axioms greedy_full_rank
#print axioms first_full_rank_query_reached
#print axioms greedy_length
#print axioms greedy_width
#print axioms actual_params
#print axioms final_source_rank_width
end Paper5.NativeEntry