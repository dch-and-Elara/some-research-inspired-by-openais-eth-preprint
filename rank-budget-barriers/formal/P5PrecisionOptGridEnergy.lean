import P5PrecisionOptArbitraryCarrier
import P5PrecisionOptEnergy

/-! Real signed-grid residue buckets for (P.8). The arbitrary weights
are the individual retained orders, not shell averages. Buckets
encode exactly "distance valuation at least i+j+1" on distinct points. -/
namespace Paper5.PrecisionOpt
open P1DyadicGrid HermiteLoss
open scoped BigOperators

abbrev NativeShell (u i : ℕ) := ↥(shell u i)

def rawShell {u i : ℕ} (t : NativeShell u i) : ℤ := t.val.val

theorem rawShell_mem {u i : ℕ} (t : NativeShell u i) : rawShell t ∈ grid (2*u) :=
  (Finset.mem_filter.mp t.val.property).1

theorem rawShell_ne_zero {u i : ℕ} (t : NativeShell u i) : rawShell t ≠ 0 :=
  (Finset.mem_filter.mp t.val.property).2.1

theorem rawShell_level {u i : ℕ} (t : NativeShell u i) : level (rawShell t)=i :=
  (Finset.mem_filter.mp t.property).2

theorem rawShell_injective (u i : ℕ) : Function.Injective (@rawShell u i) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem shell_oddFactor {u i : ℕ} (t : NativeShell u i) :
    ∃ w : ℤ, rawShell t=pow₂ i*(2*w+1) := by
  obtain ⟨d,ho,he⟩ := (level_iff_odd_multiplier (rawShell_ne_zero t) i).mp (rawShell_level t)
  obtain ⟨w,hw⟩ := ho
  exact ⟨w,by rw [he,hw]⟩

noncomputable def shellHalf {u i : ℕ} (t : NativeShell u i) : ℤ := (shell_oddFactor t).choose

theorem shellHalf_factor {u i : ℕ} (t : NativeShell u i) :
    rawShell t=pow₂ i*(2*shellHalf t+1) := (shell_oddFactor t).choose_spec

theorem shellHalf_diff {u i : ℕ} (t s : NativeShell u i) :
    rawShell t-rawShell s=pow₂ (i+1)*(shellHalf t-shellHalf s) := by
  rw [shellHalf_factor t,shellHalf_factor s,pow₂_succ]
  ring

noncomputable def shellBucket {u i : ℕ} (j : ℕ) (t : NativeShell u i) : Fin (2^j) :=
  ⟨(shellHalf t % pow₂ j).toNat,by
    have h0 := Int.emod_nonneg (shellHalf t) (pow₂_pos j).ne'
    have ht := Int.emod_lt_of_pos (shellHalf t) (pow₂_pos j)
    have hp : (pow₂ j:ℤ) = ((2^j:ℕ):ℤ) := by simp [pow₂]
    rw [←Int.toNat_of_nonneg h0,hp] at ht
    rw [hp]
    exact_mod_cast ht⟩

theorem shellBucket_eq_iff {u i : ℕ} (j : ℕ) (t s : NativeShell u i) :
    shellBucket j t=shellBucket j s ↔ pow₂ j∣shellHalf t-shellHalf s := by
  have h0 := Int.emod_nonneg (shellHalf t) (pow₂_pos j).ne'
  have h1 := Int.emod_nonneg (shellHalf s) (pow₂_pos j).ne'
  have hl : shellBucket j t=shellBucket j s ↔
      shellHalf s ≡ shellHalf t [ZMOD pow₂ j] := by
    unfold shellBucket
    constructor
    · intro h
      have h' := congrArg (fun f : Fin (2^j) => ((f.val:ℕ):ℤ)) h
      change ((shellHalf t % pow₂ j).toNat:ℤ)=((shellHalf s % pow₂ j).toNat:ℤ) at h'
      rw [Int.toNat_of_nonneg h0,Int.toNat_of_nonneg h1] at h'
      exact h'.symm
    · intro h
      exact Fin.ext (congrArg Int.toNat h.symm)
  exact hl.trans Int.modEq_iff_dvd

theorem shellBucket_is_threshold {u i : ℕ} (j : ℕ) (t s : NativeShell u i) (hne : t≠s) :
    shellBucket j t=shellBucket j s ↔ j<level (rawShell t-rawShell s)-i := by
  rw [shellBucket_eq_iff]
  have hp : pow₂ (i+j+1) = pow₂ (i+1)*pow₂ j := by
    unfold pow₂
    rw [←pow_add]
    congr 1
    omega
  have he : (pow₂ j∣shellHalf t-shellHalf s) ↔ pow₂ (i+j+1)∣rawShell t-rawShell s := by
    rw [hp,shellHalf_diff, mul_dvd_mul_iff_left (pow₂_pos (i+1)).ne']
  rw [he]
  have hz : rawShell t-rawShell s≠0 := sub_ne_zero.mpr (fun h => hne (rawShell_injective u i h))
  constructor
  · intro h
    have ht := ((padicValInt_dvd_iff (p:=2) (i+j+1) _).mp h).resolve_left hz
    change i+j+1≤level (rawShell t-rawShell s) at ht
    omega
  · intro h
    apply (padicValInt_dvd_iff (p:=2) (i+j+1) _).mpr
    right
    change i+j+1≤level (rawShell t-rawShell s)
    omega

theorem fin_count_below (n D : ℕ) (hD : D≤n) :
    (∑ j : Fin n,if j.val<D then (1:ℕ) else 0)=D := by
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j<D then (1:ℕ) else 0)]
  have he : ((Finset.range n).filter (fun j => j<D))=Finset.range D := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [←Finset.sum_filter,he]
  simp

def shellDistance {u i : ℕ} (t s : NativeShell u i) : ℕ :=
  level (rawShell t-rawShell s)-i

theorem shellDistance_thresholds {u i : ℕ} (t s : NativeShell u i) (hne : t≠s) :
    shellDistance t s = ∑ j : Fin (2*u-i),if shellBucket j.val t=shellBucket j.val s then (1:ℕ) else 0 := by
  have hd := level_difference_le (rawShell_mem t) (rawShell_mem s)
    (fun h => hne (rawShell_injective u i h))
  have h := fin_count_below (2*u-i) (shellDistance t s)
    (Nat.sub_le_sub_right hd i)
  simpa only [shellBucket_is_threshold _ t s hne] using h.symm

theorem actual_grid_p8 {u i : ℕ} (w : NativeShell u i→ℚ) :
    2*(1-(1:ℚ)/2^(2*u-i))*(∑ t,w t)^2 ≤
      (∑ t,∑ s∈Finset.univ.erase t,w t*w s*(shellDistance t s:ℚ))+
        ((2*u-i:ℕ):ℚ)*(∑ t,w t^2) := by
  let n := 2*u-i
  let W := ∑ t,w t
  let m (j : Fin n) : ℕ := 2^j.val
  have H := arbitrary_weight_p8 (J:=Fin n) shellDistance w m
    (fun j => shellBucket j.val) (fun _ => by dsimp [m]; positivity)
    (fun t s h => shellDistance_thresholds t s (Ne.symm h))
  rw [Fintype.card_fin] at H
  have he : (∑ j : Fin n, W^2/(m j:ℚ)) = 2*(1-(1:ℚ)/2^n)*W^2 := by
    calc
      _ = W^2*∑ j : Fin n, (1:ℚ)/2^j.val := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp [m,div_eq_mul_inv]
      _ = _ := by rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (1:ℚ)/2^j),dyadic_reciprocal_sum]; ring
  rw [←he]
  exact H

#print axioms shellBucket_eq_iff
#print axioms shellBucket_is_threshold
#print axioms shellDistance_thresholds
#print axioms actual_grid_p8
end Paper5.PrecisionOpt
