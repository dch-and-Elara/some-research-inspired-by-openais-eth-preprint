import J6ChildGroup

namespace J6ChildIdentity
open scoped BigOperators Classical
open J6ActiveAllocation J6ActiveProfile J6FixedProfile J6SourceMoment J6ChildGroup
variable {R I M K G : Type*} [CommRing R] [Fintype I] [Fintype M] [Fintype K] [Fintype G]
variable {Val : G → Type*} [∀ g, Fintype (Val g)]

abbrev Profile (I M : Type*) [Fintype I] := M → Fin (Fintype.card I + 1)

noncomputable def localizedCoeff
    (w : M → ℕ) (block : I → K) (target : M → K) (atTarget : K → G)
    (row : ∀ i, Val (atTarget (block i)) → Option M → R)
    (b : Profile I M) (k : K) (v : Val (atTarget k)) : R :=
  ∑ y : J6BlockFactor.rows block k → Option M,
    if test block target b k y then
      ∏ i : J6BlockFactor.rows block k,
        scaled w (fun _ z => row i.val ((congrArg atTarget i.property).symm ▸ v) z) i.val (y i)
    else 0

omit [Fintype K] [Fintype G] [∀ g, Fintype (Val g)] in
theorem coefficient_is_local
    (w : M → ℕ) (block : I → K) (target : M → K) (atTarget : K → G)
    (row : ∀ i, Val (atTarget (block i)) → Option M → R)
    (b : Profile I M) (k : K) (x : ∀ g, Val g) :
    targetCoeff w (fun i => row i (x (atTarget (block i)))) block target b k =
      localizedCoeff w block target atTarget row b k (x (atTarget k)) := by
  classical
  unfold targetCoeff localizedCoeff
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases h : test block target b k y
  · rw [if_pos h, if_pos h]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rcases i with ⟨i, hi⟩
    change block i = k at hi
    subst k
    rfl
  · rw [if_neg h, if_neg h]

set_option maxHeartbeats 1000000 in
/-- The nonzero probe's local contraction, after row-factor expansion and
before binary interpolation. This starts from actual affine row factors:
their weight bounds and locality, not the final child identity, are inputs. -/
theorem exact_grouped_mode_contraction
    (w : M → ℕ) (p : ℕ) (hp : (2:R)^p = 0)
    (block : I → K) (target : M → K) (atTarget : K → G) (atSource : M → G)
    (row : ∀ i, Val (atTarget (block i)) → Option M → R)
    (old : ∀ g, Val g → R) (L : ∀ m, Val (atSource m) → R)
    (hzero : ∀ i m v, block i ≠ target m → row i v (some m) = 0) :
    (∑ x : ∀ g, Val g, (∏ g, old g (x g)) *
      (∏ i, ∑ v : Option M, scaled w
        (insert (fun i => row i (x (atTarget (block i)))) (fun m => L m (x (atSource m)))) i v)) =
    ∑ b : Profile I M, if profileWeight w b < p then
      ∏ g, ∑ y : Val g, old g y *
        (∏ m : J6BlockFactor.rows atSource g, L m.val (m.property.symm ▸ y) ^ (b m.val).val) *
        (∏ k : J6BlockFactor.rows atTarget g,
          localizedCoeff w block target atTarget row b k.val (k.property.symm ▸ y))
      else 0 := by
  classical
  trans ∑ x : ∀ g, Val g, ∑ b : Profile I M,
    if profileWeight w b < p then
      (∏ g, old g (x g)) * (∏ m, L m (x (atSource m)) ^ (b m).val) *
        (∏ k, localizedCoeff w block target atTarget row b k (x (atTarget k)))
    else 0
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [sum_modes_with_moments w _ _ p hp block target (fun i m => hzero i m _),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : profileWeight w b < p
    · simp only [if_pos hb, coefficient_is_local, mul_assoc]
    · simp only [if_neg hb, mul_zero]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hb : profileWeight w b < p
    · simp only [if_pos hb]
      exact contract_grouped atTarget atSource old
        (localizedCoeff w block target atTarget row b) (fun m v => L m v ^ (b m).val)
    · simp only [if_neg hb, Finset.sum_const_zero]

#print axioms coefficient_is_local
#print axioms exact_grouped_mode_contraction
end J6ChildIdentity
