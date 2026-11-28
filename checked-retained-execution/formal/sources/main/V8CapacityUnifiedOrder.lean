import V8CapacityUnifiedObservation

/-! The actual order on O/(πᵖ), including zero. It is not a hypothesized
order array on an integral target. Membership agrees for every integral
lift, because all admissible exponents are at most p. -/
namespace V8CapacityUnified
open scoped Classical
open V8CapacityCRTJet

noncomputable section
set_option linter.unusedSectionVars false

variable {O : Type*} [CommRing O]

def orderSet (π : O) (p : ℕ) (v : BaseMod O π p) : Finset ℕ :=
  (Finset.range (p+1)).filter (fun t => coeffMod O π p (π^t)∣v)

theorem mem_orderSet (π : O) (p : ℕ) (v : BaseMod O π p) (t : ℕ) :
    t∈orderSet π p v ↔ t≤p ∧ coeffMod O π p (π^t)∣v := by
  simp [orderSet,Nat.lt_succ_iff]

theorem orderSet_nonempty (π : O) (p : ℕ) (v : BaseMod O π p) :
    (orderSet π p v).Nonempty :=
  ⟨0,(mem_orderSet π p v 0).mpr ⟨Nat.zero_le _,by simp⟩⟩

/-- ν_p, the maximal order still distinguishable at precision p. -/
def truncatedOrder (π : O) (p : ℕ) (v : BaseMod O π p) : ℕ :=
  (orderSet π p v).max' (orderSet_nonempty π p v)

theorem order_le_precision (π : O) (p : ℕ) (v : BaseMod O π p) :
    truncatedOrder π p v≤p :=
  ((mem_orderSet π p v _).mp (Finset.max'_mem _ _)).1

theorem order_ge_iff (π : O) (p : ℕ) (v : BaseMod O π p) {t : ℕ} (ht : t≤p) :
    t≤truncatedOrder π p v ↔ coeffMod O π p (π^t)∣v := by
  have hM := ((mem_orderSet π p v (truncatedOrder π p v)).mp (Finset.max'_mem _ _)).2
  constructor
  · intro h
    have hd : coeffMod O π p (π^t)∣coeffMod O π p (π^truncatedOrder π p v) := by
      obtain ⟨u,hu⟩ := pow_dvd_pow π h
      exact ⟨coeffMod O π p u,by rw [hu,map_mul]⟩
    exact hd.trans hM
  · intro h
    exact Finset.le_max' _ _ ((mem_orderSet π p v t).mpr ⟨ht,h⟩)

theorem order_full_iff_zero (π : O) (p : ℕ) (v : BaseMod O π p) :
    truncatedOrder π p v=p ↔ v=0 := by
  have hz : coeffMod O π p (π^p)=0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span (by simp)
  constructor
  · intro h
    have hd := (order_ge_iff π p v (t:=p) le_rfl).mp (by omega)
    rwa [hz,zero_dvd_iff] at hd
  · intro h
    have hl := (order_ge_iff π p v (t:=p) le_rfl).mpr (by rw [h]; exact dvd_zero _)
    exact le_antisymm (order_le_precision π p v) hl

theorem order_in_exact_stratum (π : O) (p : ℕ) (v : BaseMod O π p) {t : ℕ} (ht : t<p) :
    truncatedOrder π p v=t ↔
      v∈Ideal.span ({coeffMod O π p (π^t)}:Set (BaseMod O π p)) ∧
      v∉Ideal.span ({coeffMod O π p (π^(t+1))}:Set (BaseMod O π p)) := by
  simp only [Ideal.mem_span_singleton,← order_ge_iff π p v (Nat.le_of_lt ht),
    ← order_ge_iff π p v (Nat.succ_le_of_lt ht)]
  omega

/-- The actual order is independent of the choice of lift. -/
theorem order_of_lift_iff (π : O) (p : ℕ) (x : O) {t : ℕ} (ht : t≤p) :
    t≤truncatedOrder π p (coeffMod O π p x) ↔ π^t∣x := by
  rw [order_ge_iff π p _ ht]
  constructor
  · rintro ⟨v,hv⟩
    obtain ⟨a,rfl⟩ := Ideal.Quotient.mk_surjective v
    change coeffMod O π p x = coeffMod O π p (π^t)*coeffMod O π p a at hv
    rw [← map_mul] at hv
    have hd := (residues_eq_iff π p _ _).mp hv
    have h₁ : π^t∣x-π^t*a := (pow_dvd_pow π ht).trans hd
    have h₂ : π^t∣π^t*a := dvd_mul_right _ _
    simpa only [sub_add_cancel] using dvd_add h₁ h₂
  · rintro ⟨a,ha⟩
    exact ⟨coeffMod O π p a,by rw [ha,map_mul]⟩

#print axioms order_le_precision
#print axioms order_ge_iff
#print axioms order_full_iff_zero
#print axioms order_in_exact_stratum
#print axioms order_of_lift_iff
end
end V8CapacityUnified
