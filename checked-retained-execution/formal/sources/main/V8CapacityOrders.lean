import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic

/-! Finite precision orders by complete congruence depth. This supplies
exact unit factors below saturation, including in mixed characteristic. -/
namespace V8CapacityOrders
open scoped BigOperators Classical
noncomputable section
variable {O : Type*} [CommRing O]

def hits (π : O) (B : ℕ) (x : O) : Finset ℕ :=
  (Finset.range B).filter (fun u => π^(u+1)∣x)

def ord (π : O) (B : ℕ) (x : O) : ℕ := (hits π B x).card

theorem ord_le (π : O) (B : ℕ) (x : O) : ord π B x≤B := by
  simpa only [ord,hits,Finset.card_range] using
    Finset.card_filter_le (Finset.range B) (fun u => π^(u+1)∣x)

theorem ord_as_sum (π : O) (B : ℕ) (x : O) :
    ord π B x = ∑ u ∈ Finset.range B, if π^(u+1)∣x then 1 else 0 :=
  Finset.card_filter _ _

theorem ord_iff (π : O) (B : ℕ) (x : O) (u : ℕ) (hu : u≤B) :
    π^u∣x ↔ u≤ord π B x := by
  constructor
  · intro h
    have hsub : Finset.range u ⊆ hits π B x := by
      intro i hi
      have hiu := Finset.mem_range.mp hi
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (hiu.trans_le hu),(pow_dvd_pow π (Nat.succ_le_of_lt hiu)).trans h⟩
    simpa only [Finset.card_range,ord] using Finset.card_le_card hsub
  · intro h
    by_contra hn
    have he : u≠0 := by rintro rfl; simp at hn
    have hsub : hits π B x ⊆ Finset.range (u-1) := by
      intro i hi
      apply Finset.mem_range.mpr
      have heq : ¬(u ≤ i+1) := fun hl =>
        hn ((pow_dvd_pow π hl).trans (Finset.mem_filter.mp hi).2)
      omega
    have hc := Finset.card_le_card hsub
    change ord π B x ≤ (Finset.range (u-1)).card at hc
    rw [Finset.card_range] at hc
    omega

theorem ord_dvd (π : O) (B : ℕ) (x : O) : π^(ord π B x)∣x :=
  (ord_iff π B x _ (ord_le π B x)).mpr le_rfl

theorem ord_lt_of_failed (π : O) (B : ℕ) (x : O) (hn : ¬π^B∣x) : ord π B x<B :=
  lt_of_not_ge (fun hb => hn ((ord_iff π B x B le_rfl).mpr hb))

variable [IsLocalRing O]

theorem ord_unit_factor (π : O)
    (hπ : IsLocalRing.maximalIdeal O = Ideal.span ({π}:Set O))
    (B : ℕ) (x : O) (hn : ¬π^B∣x) :
    ∃ u : Oˣ, x = π^(ord π B x)*(u:O) := by
  obtain ⟨y,hy⟩ := ord_dvd π B x
  have hu : IsUnit y := by
    apply (IsLocalRing.notMem_maximalIdeal).mp
    intro hY
    have hPy : π∣y := by
      rwa [hπ,Ideal.mem_span_singleton] at hY
    obtain ⟨z,hz⟩ := hPy
    have hd : π^(ord π B x+1)∣x := by
      refine ⟨z,?_⟩
      calc
        x = π^(ord π B x)*y := hy
        _ = π^(ord π B x+1)*z := by rw [hz,pow_succ,mul_assoc]
    have hlt := ord_lt_of_failed π B x hn
    have hh := (ord_iff π B x _ (Nat.succ_le_of_lt hlt)).mp hd
    omega
  exact ⟨hu.unit, by rw [hu.unit_spec]; exact hy⟩

#print axioms ord_le
#print axioms ord_as_sum
#print axioms ord_iff
#print axioms ord_dvd
#print axioms ord_unit_factor
end
end V8CapacityOrders
