import V8CapacitySpecialResidueJet
import V8CapacityDigitNodes

/-! J6 per-alpha exact count, using the maximal common characteristic
power and an actual finite bijection with the allowable offsets. -/
namespace V8CapacitySpecialJ6
open scoped Classical BigOperators
open V8CapacitySymbolic V8CapacitySpecialResidueJet

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000

variable {H K : Type*} [Field K] [Fintype H]
variable {k : ℕ} (c : ℕ) [Fact c.Prime] [CharP K c]
variable [ExpChar (MvPolynomial (Digits H k) K) c]

def breakRow (α : H → ℕ) (n : ℕ) : Prop :=
  ∃ i : H, ¬c^(n+1)∣α i

theorem common_power_break (α : H → ℕ) (ha : α≠0) : ∃ n, breakRow c α n := by
  have h : ∃ i, α i≠0 := by
    by_contra! he
    apply ha
    funext i
    exact he i
  obtain ⟨i,hi⟩ := h
  refine ⟨α i, i,?_⟩
  intro hd
  have hD := Nat.le_of_dvd (Nat.pos_of_ne_zero hi) hd
  have hl := V8CapacityDigits.successor_le_pow c (Fact.out : c.Prime).two_le (α i+1)
  omega

def commonExponent (α : H → ℕ) (ha : α≠0) : ℕ :=
  Nat.find (common_power_break c α ha)

abbrev commonPower (α : H → ℕ) (ha : α≠0) : ℕ := c^commonExponent c α ha

def normalizedExponents (α : H → ℕ) (ha : α≠0) (i : H) : ℕ :=
  α i/commonPower c α ha

theorem common_divides (α : H → ℕ) (ha : α≠0) (i : H) :
    commonPower c α ha∣α i := by
  by_cases h : commonExponent c α ha=0
  · change c^commonExponent c α ha∣α i
    rw [h,pow_zero]
    exact one_dvd _
  · obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero h
    change c^commonExponent c α ha∣α i
    rw [hn]
    by_contra hd
    exact Nat.find_min (common_power_break c α ha)
      (by show n<commonExponent c α ha; omega) ⟨i,hd⟩

theorem common_decomposition (α : H → ℕ) (ha : α≠0) (i : H) :
    α i=commonPower c α ha*normalizedExponents c α ha i := by
  unfold normalizedExponents
  exact (Nat.mul_div_cancel' (common_divides c α ha i)).symm

theorem primitive_row (α : H → ℕ) (ha : α≠0) :
    ∃ i : H, (normalizedExponents c α ha i : K)≠0 := by
  obtain ⟨i,hi⟩ := Nat.find_spec (common_power_break c α ha)
  refine ⟨i,?_⟩
  intro hz
  have h := (CharP.cast_eq_zero_iff K c _).mp hz
  obtain ⟨b,hb⟩ := h
  apply hi
  change c^(commonExponent c α ha+1)∣α i
  refine ⟨b,?_⟩
  rw [common_decomposition c α ha i,hb,pow_succ,mul_assoc]

theorem card_offsets (w d k : ℕ) (hw : w<k) (hd : 0<d) :
    Fintype.card {j : Fin k // ∃ t : ℕ, j.val=w+d*t}=1+(k-1-w)/d := by
  let f (t : Fin (1+(k-1-w)/d)) : {j : Fin k // ∃ t : ℕ, j.val=w+d*t} :=
    ⟨⟨w+d*t.val,by
      have h₁ : t.val ≤ (k-1-w)/d := by have h := t.isLt; omega
      have h₂ := (Nat.le_div_iff_mul_le hd).mp h₁
      rw [mul_comm t.val d] at h₂
      omega⟩,⟨t.val,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      apply Fin.ext
      have he := congrArg (fun z : {j : Fin k // ∃ t : ℕ, j.val=w+d*t} => z.val.val) h
      change w+d*x.val=w+d*y.val at he
      exact Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel he)
    · intro j
      obtain ⟨t,ht⟩ := j.property
      have h₁ := j.val.isLt
      have h₂ : t*d≤ k-1-w := by rw [mul_comm t d]; omega
      have h₃ := (Nat.le_div_iff_mul_le hd).mpr h₂
      refine ⟨⟨t,by omega⟩,?_⟩
      apply Subtype.ext
      exact Fin.ext ht.symm
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).symm.trans (Fintype.card_fin _)

theorem exact_count_nonzero_alpha (α : H → ℕ) (ha : α≠0) (hs : (∑ i : H,α i)<k) :
    Fintype.card {j : Fin k // feature (0:K) k α j.val≠0} =
      1+(k-1-(∑ i : H, α i))/commonPower c α ha := by
  obtain ⟨i,hi⟩ := primitive_row (K:=K) c α ha
  let d := commonPower c α ha
  have hc : 0<c := (Fact.out : Nat.Prime c).pos
  have h (j : Fin k) :
      feature (0:K) k α j.val≠0 ↔ ∃ t : ℕ, j.val=(∑ i : H, α i)+d*t :=
    frobenius_support_exact hc (commonExponent c α ha) α (normalizedExponents c α ha)
      (common_decomposition c α ha) i hi j.val j.isLt
  let e : {j : Fin k // feature (0:K) k α j.val≠0} ≃
      {j : Fin k // ∃ t : ℕ, j.val=(∑ i : H,α i)+d*t} :=
    { toFun := fun j => ⟨j.val,(h j.val).mp j.property⟩
      invFun := fun j => ⟨j.val,(h j.val).mpr j.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Fintype.card_congr e).trans (card_offsets _ d k hs (pow_pos hc _))

#print axioms common_decomposition
#print axioms primitive_row
#print axioms card_offsets
#print axioms exact_count_nonzero_alpha
end
end V8CapacitySpecialJ6

