import P2PublishedFiltrationEq9

/-! Exact origin filtration identity. The kernel of origin evaluation
on I_j is X·I_{j−1}, as a linear equivalence, not a dimension assumption. -/
namespace Reconstruction.LayoutMismatch.PublishedFiltration
open Polynomial
open LayoutBudget (GroupFiber)
open scoped BigOperators Polynomial
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section

variable {I V G : Type*} [Fintype I] [DecidableEq I]

def mulXCoordinates : Polys V I →ₗ[ℚ] Polys V I where
  toFun h a := X * h a
  map_add' a b := by funext i; exact mul_add X (a i) (b i)
  map_smul' c h := by funext i; simp

theorem mulXCoordinates_apply (h : Polys V I) (a : V × Mask I) :
    mulXCoordinates h a = X * h a := rfl

theorem degree_lt_mulX_iff (q : ℚ[X]) (n : ℕ) :
    (X*q).degree < ((n+1:ℕ):WithBot ℕ) ↔ q.degree < n := by
  by_cases hq : q = 0
  · subst q
    rw [mul_zero]
    exact iff_of_true (mem_degreeLT.mp ((degreeLT ℚ (n+1)).zero_mem))
      (mem_degreeLT.mp ((degreeLT ℚ n).zero_mem))
  rw [degree_eq_natDegree (mul_ne_zero X_ne_zero hq), degree_eq_natDegree hq,
    Nat.cast_lt, Nat.cast_lt,
    natDegree_mul X_ne_zero hq, natDegree_X]
  omega

theorem root_divisible_coordinate_at_zero
    (nodes : I → ℚ) (hn : ∀ t, nodes t ≠ 0) (s : Mask I) (n : ℕ)
    (p : ℚ[X]) (hp : p ∈ slotSpace nodes s (n+1)) (hz : p.eval 0 = 0) :
    ∃ q, p = X*q ∧ q ∈ slotSpace nodes s n := by
  obtain ⟨hd,c,hc⟩ := (mem_slotSpace nodes s (n+1) p).1 hp
  have hz' : c.eval 0 = 0 := by
    rw [hc,eval_mul] at hz
    exact (mul_eq_zero.mp hz).resolve_left (rootProduct_atZero_ne nodes s hn)
  have xdiv : (X : ℚ[X]) ∣ c := X_dvd_iff.mpr ((coeff_zero_eq_eval_zero c).trans hz')
  obtain ⟨d,hdiv⟩ := xdiv
  let q := rootProduct nodes s * d
  have exactEq : p = X*q := by rw [hc,hdiv]; dsimp only [q]; ring
  have hxDegree : (X*q).degree < ((n+1:ℕ):WithBot ℕ) := by rw [← exactEq]; exact hd
  have dq := (degree_lt_mulX_iff q n).1 hxDegree
  exact ⟨q,exactEq,(mem_slotSpace nodes s n q).2 ⟨dq,d,rfl⟩⟩

variable [Fintype G] [DecidableEq G] [Fintype V]
variable (nodes : I → ℚ) (a b : I → V → G)
variable {Rows : I → G → Type*} [∀ t g, Fintype (Rows t g)]
variable (C : ∀ t g, Matrix (Rows t g) (GroupFiber (a t) g) ℚ)

theorem tensorAt_mulX (h : Polys V I) (v : V) (x : Mask I) (z : ℚ) :
    tensorAt a b (mulXCoordinates h) v x z = z * tensorAt a b h v x z := by
  unfold tensorAt
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  simp only [mulXCoordinates_apply, eval_mul, eval_X]
  ring

theorem full_check_mulX (h : Polys V I) (t : I) (g : G) (x : Mask I) (i : Rows t g) :
    fullNodalChecks nodes a b C (mulXCoordinates h) t g x i =
      nodes t * fullNodalChecks nodes a b C h t g x i := by
  simp only [full_nodal_check_coord, tensorAt_mulX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem mulX_stays_in_next_kernel (n : ℕ) {h : Polys V I} (hh : h ∈ Ilt nodes a b C n) :
    mulXCoordinates h ∈ Ilt nodes a b C (n+1) := by
  obtain ⟨hH,hk⟩ := (mem_Ilt nodes a b C n h).1 hh
  apply (mem_Ilt nodes a b C (n+1) _).2
  refine ⟨(mem_Hlt nodes (n+1) _).2 ?_,?_⟩
  · intro v s
    obtain ⟨deg,q,hq⟩ := (mem_Hlt nodes n h).1 hH v s
    refine ⟨(degree_lt_mulX_iff (h (v,s)) n).2 deg, X*q,?_⟩
    rw [mulXCoordinates_apply,hq]
    ring
  · intro t g x i
    rw [full_check_mulX,hk t g x i,mul_zero]

def originValues (n : ℕ) : Ilt nodes a b C n →ₗ[ℚ] (V × Mask I → ℚ) where
  toFun h q := (h.val q).eval 0
  map_add' h f := by funext q; exact eval_add
  map_smul' c h := by
    funext q
    change (c • h.val q).eval 0 = c * (h.val q).eval 0
    rw [smul_eq_C_mul, eval_mul, eval_C]

def timesXIntoOriginKernel (n : ℕ) :
    Ilt nodes a b C n →ₗ[ℚ] LinearMap.ker (originValues nodes a b C (n+1)) where
  toFun h :=
    ⟨⟨mulXCoordinates h.val,mulX_stays_in_next_kernel nodes a b C n h.property⟩,by
      rw [LinearMap.mem_ker]
      funext q
      change (X * h.val q).eval 0 = 0
      simp⟩
  map_add' h f := Subtype.ext (Subtype.ext (map_add mulXCoordinates h.val f.val))
  map_smul' z h := Subtype.ext (Subtype.ext (map_smul mulXCoordinates z h.val))

/-- Evaluation at zero has an actual linear kernel isomorphism, including
the n=0 boundary. Nonzero nodes are used only where division requires it. -/
def originKernelEquiv (n : ℕ) (hn : ∀ t, nodes t ≠ 0) :
    Ilt nodes a b C n ≃ₗ[ℚ] LinearMap.ker (originValues nodes a b C (n+1)) := by
  classical
  apply LinearEquiv.ofBijective (timesXIntoOriginKernel nodes a b C n)
  constructor
  · intro f h eq
    apply Subtype.ext
    funext q
    apply mul_left_cancel₀ (a:=X) (X_ne_zero (R:=ℚ))
    exact congrArg (fun z : LinearMap.ker (originValues nodes a b C (n+1)) => z.val.val q) eq
  · intro f
    let p := f.val.val
    have hI := (mem_Ilt nodes a b C (n+1) p).1 f.val.property
    have atZero : originValues nodes a b C (n+1) f.val = 0 := LinearMap.mem_ker.mp f.property
    have allCoord (z : V × Mask I) : ∃ q, p z = X*q ∧ q ∈ slotSpace nodes z.2 n :=
      root_divisible_coordinate_at_zero nodes hn z.2 n (p z)
        ((mem_slotSpace nodes z.2 (n+1) (p z)).2
          ((mem_Hlt nodes (n+1) p).1 hI.1 z.1 z.2))
        (congrFun atZero z)
    choose q exactEq valid using allCoord
    have same : p = mulXCoordinates q := funext exactEq
    have qI : q ∈ Ilt nodes a b C n := by
      refine (mem_Ilt nodes a b C n q).2 ⟨?_,?_⟩
      · exact (mem_Hlt nodes n q).2 (fun v s =>
          (mem_slotSpace nodes s n (q (v,s))).1 (valid (v,s)))
      · intro t g x i
        apply (mul_eq_zero.mp ?_).resolve_left (hn t)
        rw [← full_check_mulX, ← same]
        exact hI.2 t g x i
    exact ⟨⟨q,qI⟩, Subtype.ext (Subtype.ext same.symm)⟩

theorem Ilt_zero : Ilt nodes a b C 0 = ⊥ := by
  simp [Ilt,Hlt_zero]

instance IltFinite (n : ℕ) : FiniteDimensional ℚ (Ilt nodes a b C n) :=
  FiniteDimensional.of_injective
    (Submodule.inclusion (show Ilt nodes a b C n ≤ Hlt nodes n from inf_le_left))
    (Submodule.inclusion_injective _)

theorem origin_dim_increment (n : ℕ) (hn : ∀ t, nodes t ≠ 0) :
    Module.finrank ℚ (Ilt nodes a b C (n+1)) - Module.finrank ℚ (Ilt nodes a b C n) =
      Module.finrank ℚ (LinearMap.range (originValues nodes a b C (n+1))) := by
  have hr := (originValues nodes a b C (n+1)).finrank_range_add_finrank_ker
  rw [← (originKernelEquiv nodes a b C n hn).finrank_eq] at hr
  omega

#print axioms degree_lt_mulX_iff
#print axioms root_divisible_coordinate_at_zero
#print axioms full_check_mulX
#print axioms timesXIntoOriginKernel
#print axioms originKernelEquiv
#print axioms Ilt_zero
#print axioms origin_dim_increment
end
end Reconstruction.LayoutMismatch.PublishedFiltration

