import PTAdmissibility

namespace RootSeparation.Preprocessing

open S11 Finset
open scoped BigOperators

/-- The total multiplicity exceeds the degree cap before unit-denominator
Lagrange interpolation and tapered Hermite recovery are invoked. -/
theorem hermite_mass {s d M : ℕ} (checks : ActiveNumbers s d M) :
    M*(2*packetLength s d-1) <
      ∑ t ∈ centers (retained s d) (packetLength s d), multiplicity M (retained s d) t := by
  let L := packetLength s d
  let u := retained s d
  have hu : 0 < u := checks.retainedPos
  have hM : 0 < M := hu.trans_le checks.retainedLeWire
  have ha : 0 < labelLength s d := hu.trans_le checks.retainedLeLabel
  have hL : 0 < L := by unfold L packetLength; positivity
  obtain ⟨k,hk⟩ : ∃ k : ℕ, L = 2*k := by
    refine ⟨2^(labelLength s d-1),?_⟩
    change 2^labelLength s d = _
    conv_lhs => rw [show labelLength s d = (labelLength s d-1)+1 by omega]
    rw [pow_succ,Nat.mul_comm]
  let f : Fin L ↪ ℤ :=
    ⟨fun i => 2*(i.val : ℤ)-(L : ℤ)+1, by
      intro a b h
      apply Fin.ext
      change 2*(a.val : ℤ)-(L : ℤ)+1 = 2*(b.val : ℤ)-(L : ℤ)+1 at h
      omega⟩
  have hlevel (i : Fin L) : level (f i) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    have hh : ¬ (2 : ℤ) ∣ f i := by
      rintro ⟨b,hb⟩
      change 2*(i.val : ℤ)-(L : ℤ)+1 = 2*b at hb
      omega
    exact fun h => hh (by exact_mod_cast (Int.natAbs_dvd_natAbs.mp h))
  have hmem (i : Fin L) : f i ∈ centers u L := by
    have hi := i.isLt
    unfold centers
    rw [mem_filter,mem_Ico,hlevel]
    change (-(L:ℤ) ≤ 2*(i.val:ℤ)-(L:ℤ)+1 ∧ 2*(i.val:ℤ)-(L:ℤ)+1 < L) ∧
      2*(i.val:ℤ)-(L:ℤ)+1 ≠ 0 ∧ 0 < u
    omega
  have hm : ∀ i : Fin L, multiplicity M u (f i) = taper M u*u := by
    intro i
    unfold S11.multiplicity
    rw [hlevel,Nat.sub_zero]
  have hsum : L*(taper M u*u) ≤ ∑ t ∈ centers u L, multiplicity M u t := by
    calc
      _ = ∑ i : Fin L, multiplicity M u (f i) := by simp [hm]
      _ = ∑ t ∈ (univ : Finset (Fin L)).map f, multiplicity M u t := (sum_map _ _ _).symm
      _ ≤ _ := sum_le_sum_of_subset (by
        intro t ht
        obtain ⟨i,_,rfl⟩ := mem_map.mp ht
        exact hmem i)
  have hmul := Nat.mul_le_mul_left L (three_mul_le_taper_mul (M := M) hu)
  have hstrict : M*(2*L-1) < L*(3*M) := by
    calc
      _ ≤ M*(2*L) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = (2*M)*L := by ring
      _ < (3*M)*L := Nat.mul_lt_mul_of_pos_right (by omega) hL
      _ = _ := by ring
  exact hstrict.trans_le (hmul.trans hsum)

#print axioms hermite_mass

end RootSeparation.Preprocessing
