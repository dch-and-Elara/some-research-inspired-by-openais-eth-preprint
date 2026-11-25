import BooleanCube.Binomial

namespace LocalReconstruction
open Filter Real
open scoped Topology
noncomputable section

/-- N_q(k) in the paper, including the endpoint whose weight is one. -/
def weightedTail (q k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), ((k+1-j : ℕ):ℝ) * q.choose j

private def back (q k l : ℕ) : ℝ := if l ≤ k then q.choose (k-l) else 0

private theorem back_nonneg (q k l : ℕ) : 0 ≤ back q k l := by
  unfold back; split <;> positivity

private theorem back_step {q k : ℕ} (hk : 2*k ≤ q) (l : ℕ) :
    ((q:ℝ)-k+1)*(back q k l-back q k (l+1)) =
      ((q:ℝ)-2*k+1)*back q k l + l*(back q k l+back q k (l+1)) := by
  by_cases hl : l < k
  · let j := k-(l+1)
    have h1 : k-l = j+1 := by dsimp [j]; omega
    have hj : j ≤ q := by dsimp [j]; omega
    have h := congrArg (fun x : ℕ => (x:ℝ)) (Nat.choose_succ_right_eq q j)
    push_cast [Nat.cast_sub hj] at h
    have castj : (j:ℝ) = k-l-1 := by
      dsimp [j]; rw [Nat.cast_sub (by omega)]; push_cast; ring
    simp only [back,if_pos (Nat.le_of_lt hl),if_pos (show l+1≤k by omega),h1]
    change _ * ((q.choose (j+1):ℝ)-q.choose j) = _ * (q.choose (j+1):ℝ)+_*(q.choose (j+1)+q.choose j)
    rw [castj] at h
    linarith
  · by_cases he : l=k
    · subst l; simp [back]; ring
    · simp [back,show ¬l≤k by omega,show ¬l+1≤k by omega]

private theorem back_mono {q k : ℕ} (hk : 2*k ≤ q) (l : ℕ) :
    back q k (l+1) ≤ back q k l := by
  have ha : 0 < (q:ℝ)-k+1 := by
    have : (k:ℝ) ≤ q := by exact_mod_cast (show k≤q by omega)
    linarith
  have hg : 0 ≤ (q:ℝ)-2*k+1 := by
    have : 2*(k:ℝ) ≤ q := by exact_mod_cast hk
    linarith
  have e := back_step hk l
  apply sub_nonneg.mp
  exact nonneg_of_mul_nonneg_right (e ▸ add_nonneg (mul_nonneg hg (back_nonneg ..))
    (mul_nonneg (Nat.cast_nonneg _) (add_nonneg (back_nonneg ..) (back_nonneg ..)))) ha

private theorem tail_reflect (q k : ℕ) :
    weightedTail q k = ∑ l ∈ Finset.range (k+1), ((l:ℝ)+1)*back q k l := by
  unfold weightedTail
  rw [← Finset.sum_range_reflect (fun j => ((k+1-j : ℕ):ℝ) * q.choose j)]
  apply Finset.sum_congr rfl
  intro l hl
  have h : l ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  simp [back,h,show k+1-(k-l)=l+1 by omega]

private def moment (q k : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.range (k+1), w l * back q k l

private def defect (q k : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.range (k+1), w l * l * (back q k l + back q k (l+1))

private theorem sum_diff (f : ℕ → ℝ) (n : ℕ) :
    ∑ l ∈ Finset.range n, (f l - f (l+1)) = f 0 - f n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; ring

private theorem balance {q k : ℕ} (hk : 2*k ≤ q) (P w v : ℕ → ℝ)
    (hw : ∀ l, P (l+1) = w l) (hv : ∀ l, w l - P l = v l) :
    ((q:ℝ)-k+1)*(P 0 * back q k 0 + moment q k v) =
      ((q:ℝ)-2*k+1)*moment q k w + defect q k w := by
  have t := sum_diff (fun l => P l * back q k l) (k+1)
  have endzero : back q k (k+1) = 0 := by simp [back]
  simp only [endzero, mul_zero,sub_zero] at t
  unfold moment defect
  rw [← t,← Finset.sum_add_distrib,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [hw,←hv]
  linear_combination w l * back_step hk l

private theorem defect_le {q k : ℕ} (hk : 2*k ≤ q) (w v : ℕ → ℝ) (c : ℝ)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 2*w i*i ≤ c*v i) :
    defect q k w ≤ c * moment q k v := by
  unfold defect moment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ w i*i*(2*back q k i) := mul_le_mul_of_nonneg_left
      (by linarith [back_mono hk i]) (mul_nonneg (hw i) (Nat.cast_nonneg i))
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right (hv i) (back_nonneg q k i)]

/-- Two exact finite bounds for the weighted tail. Their relative gap tends to zero
throughout the moderate-deviation window. -/
theorem weighted_tail_sandwich {q k : ℕ} (hk : 2*k ≤ q) :
    let a : ℝ := (q:ℝ)-2*k+1
    let A : ℝ := (q:ℝ)-k+1
    a^2 * weightedTail q k ≤ A^2 * q.choose k ∧
      A^2 * q.choose k ≤ (a^2 + 6*A)*weightedTail q k := by
  dsimp only
  let w₀ := fun _ : ℕ => (1:ℝ)
  let w₁ := fun l : ℕ => (l:ℝ)+1
  let w₂ := fun l : ℕ => ((l:ℝ)+1)*((l:ℝ)+2)/2
  have e₀ := balance hk w₀ w₀ (fun _ => 0) (fun _ => rfl) (fun _ => sub_self 1)
  have e₁ := balance hk (fun l => (l:ℝ)) w₁ w₀ (fun l => by simp [w₁])
    (fun l => by simp [w₀,w₁])
  have e₂ := balance hk (fun l => (l:ℝ)*((l:ℝ)+1)/2) w₂ w₁
    (fun l => by dsimp [w₂]; push_cast; ring) (fun l => by dsimp [w₂,w₁]; ring)
  have h₀ := defect_le hk w₀ w₁ 2 (fun _ => zero_le_one) (fun i => by dsimp [w₀,w₁]; linarith)
  have h₁ := defect_le hk w₁ w₂ 4 (fun _ => by dsimp [w₁]; positivity)
    (fun i => by dsimp [w₁,w₂]; nlinarith [Nat.cast_nonneg (α:=ℝ) i])
  have pos (w : ℕ → ℝ) (h : ∀ i, 0 ≤ w i) : 0 ≤ defect q k w := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (mul_nonneg (h i) (Nat.cast_nonneg _)) (add_nonneg (back_nonneg ..) (back_nonneg ..))
  have Apos : 0 ≤ (q:ℝ)-k+1 := by
    have : (k:ℝ) ≤ q := by exact_mod_cast (show k ≤ q by omega)
    linarith
  have apos : 0 ≤ (q:ℝ)-2*k+1 := by
    have : 2*(k:ℝ) ≤ q := by exact_mod_cast hk
    linarith
  have e : weightedTail q k = moment q k w₁ := tail_reflect q k
  rw [e]
  have z : moment q k (fun _ => 0) = 0 := by simp [moment]
  have b : back q k 0 = q.choose k := by simp [back]
  simp only [w₀,one_mul,z,add_zero,b] at e₀
  simp only [Nat.cast_zero,zero_mul,zero_add,zero_div] at e₁ e₂
  have x₀ := pos w₀ (fun _ => zero_le_one)
  have x₁ := pos w₁ (fun _ => by dsimp [w₁]; positivity)
  have x₂ := pos w₂ (fun _ => by dsimp [w₂]; positivity)
  change ((q:ℝ)-k+1)*(q.choose k) = ((q:ℝ)-2*k+1)*moment q k w₀ + defect q k w₀ at e₀
  constructor
  · nlinarith only [congrArg (fun x => ((q:ℝ)-k+1)*x) e₀,
      congrArg (fun x => ((q:ℝ)-2*k+1)*x) e₁,mul_nonneg Apos x₀,mul_nonneg apos x₁]
  · nlinarith only [congrArg (fun x => ((q:ℝ)-k+1)*x) e₀,
      congrArg (fun x => ((q:ℝ)-2*k+1)*x) e₁,mul_le_mul_of_nonneg_left h₀ Apos,
      mul_le_mul_of_nonneg_left h₁ apos,e₂,x₂]

end
end LocalReconstruction
