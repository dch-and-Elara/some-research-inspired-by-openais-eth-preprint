import P5PrecisionOptGridEnergy

/-! Weighted means on the actual native shells. The mean remains
defined on empty shells and is exactly zero there. -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

noncomputable def shellCellEquiv (u i : ℕ) (hi : i<u) :
    NativeShell u i ≃ ↥(levelCell (2*u) i) where
  toFun t := ⟨rawShell t,mem_levelCell.mpr ⟨rawShell_mem t,rawShell_ne_zero t,rawShell_level t⟩⟩
  invFun t := by
    let h := mem_levelCell.mp t.property
    have hlt : level t.val<u := by rw [h.2.2]; exact hi
    let r : Paper5.P3.rootNodes u :=
      ⟨t.val,Finset.mem_filter.mpr ⟨h.1,h.2.1,hlt⟩⟩
    exact ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h.2.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem native_shell_card (u i : ℕ) (hi : i<u) :
    Fintype.card (NativeShell u i) = 2^(2*u-i) := by
  rw [Fintype.card_congr (shellCellEquiv u i hi),Fintype.card_coe,level_card (by omega : i≤2*u)]

theorem native_shell_sum {G : Type*} [AddCommMonoid G] (u i : ℕ) (f : (Paper5.P3.rootNodes u)→G) :
    (∑ t : NativeShell u i,f t.val) = ∑ t∈shell u i,f t :=
  (Finset.sum_subtype (shell u i) (fun _ => Iff.rfl) f).symm

theorem native_shell_erase_sum {G : Type*} [AddCancelCommMonoid G] (u i : ℕ)
    (t : NativeShell u i) (f : (Paper5.P3.rootNodes u)→G) :
    (∑ s∈(Finset.univ : Finset (NativeShell u i)).erase t,f s.val) =
       ∑ s∈(shell u i).erase t.val,f s := by
  have h1 := Finset.sum_erase_add (Finset.univ : Finset (NativeShell u i))
    (fun s => f s.val) (Finset.mem_univ t)
  have h2 := Finset.sum_erase_add (shell u i) f t.property
  rw [native_shell_sum] at h1
  exact add_right_cancel (h1.trans h2.symm)

theorem shellCost_as_distance (u i : ℕ) (q : Profile u) (t : NativeShell u i) :
    (sameShellCost u q t.val:ℚ) =
      ∑ s∈(Finset.univ : Finset (NativeShell u i)).erase t,(q s.val:ℚ)*(shellDistance t s:ℚ) := by
  unfold sameShellCost
  have ht : level t.val.val=i := rawShell_level t
  rw [ht,Int.cast_sum,←native_shell_erase_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hd : i≤level (rawShell t-rawShell s) :=
    level_sub_ge_min
      (fun h => Finset.ne_of_mem_erase hs ((rawShell_injective u i h).symm)) i
      (rawShell_level t).ge (rawShell_level s).ge
  simp only [shellDistance,rawShell,Int.cast_mul,Int.cast_sub,Int.cast_natCast]
  change i≤level (t.val.val-s.val.val) at hd
  rw [Nat.cast_sub hd]

def shellMean (u : ℕ) (q : Profile u) (i : ℕ) : ℚ :=
  (shellOrderMass u q i:ℚ)/(2:ℚ)^(2*u-i)

theorem shellMean_nonnegative (u : ℕ) (q : Profile u) (i : ℕ) : 0≤shellMean u q i := by
  unfold shellMean
  positivity

theorem shellMean_above_native (u : ℕ) (q : Profile u) {i : ℕ} (hi : u ≤ i) :
    shellMean u q i=0 := by
  have h0 : shell u i=∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro t ht
    have he := (Finset.mem_filter.mp ht).2
    have hb := (Finset.mem_filter.mp t.property).2.2
    omega
  simp [shellMean,shellOrderMass,h0]

theorem shellMean_le_4M {u M : ℕ} (q : Profile u) (hM : u≤M)
    (hq : admissibleOrders M u q) (i : ℕ) (hi : i<u) :
    shellMean u q i ≤ 4*(M:ℚ) := by
  have h0 : shellOrderMass u q i ≤ 2^(2*u-i)*(4*M) := by
    unfold shellOrderMass
    rw [←native_shell_sum]
    calc
      (∑ t : NativeShell u i,q t.val) ≤ ∑ _t : NativeShell u i,4*M :=
        Finset.sum_le_sum fun t _ => (hq t.val).trans (q_cap M u _ hM)
      _ = _ := by
        rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,native_shell_card u i hi]
        rfl
  have h1 : (shellOrderMass u q i:ℚ) ≤ (2:ℚ)^(2*u-i)*(4*(M:ℚ)) := by exact_mod_cast h0
  unfold shellMean
  exact (div_le_iff₀ (by positivity)).mpr (h1.trans_eq (mul_comm ..))

theorem higher_gain_as_means (u : ℕ) (q : Profile u) (i : ℕ) :
    (higherShellGain u q i:ℚ)/(2:ℚ)^(2*u-i) =
      ∑ j∈Finset.range u,((j-i:ℕ):ℚ)/(2:ℚ)^(j-i)*shellMean u q j := by
  rw [shellOrderMass_grouped,Int.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hju : j<u := Finset.mem_range.mp hj
  by_cases hij : i≤j
  · have he : (2:ℚ)^(2*u-i)=(2:ℚ)^(2*u-j)*(2:ℚ)^(j-i) := by
      rw [←pow_add]
      congr 1
      omega
    simp only [shellMean,Int.cast_mul,Int.cast_natCast,he]
    ring
  · have he : j-i=0 := by omega
    simp [he]

#print axioms native_shell_card
#print axioms native_shell_erase_sum
#print axioms shellCost_as_distance
#print axioms shellMean_le_4M
#print axioms higher_gain_as_means
end Paper5.PrecisionOpt
