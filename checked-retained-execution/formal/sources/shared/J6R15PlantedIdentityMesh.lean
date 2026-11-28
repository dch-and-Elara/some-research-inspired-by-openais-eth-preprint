import J6R11RepackRootChart
import J6R11IntegralParent
import J6R10IntegralFinite
import J6NativeHeightDerivative
import J6NativeHeightDyadic

/-! The finite Cauchy matrix at the omitted probe is the positive signed
shift of the same repaired/oriented physical packet map. In particular the
padding is not reindexed through the earlier capacity chart. -/
namespace J6R15PlantedIdentity
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid P11FullPacking
open J6Mesh J6RepairedCentered J6OrientedHost J6RecursiveOrientation J6RecursiveOrientationLocal
open J6R10Repack J6R10Integral J6R11Integral J6R11Repack J6R9PacketLocal J6R9PacketCoeff
open J6R9Recursive
noncomputable section

theorem W_eval_zero {R : Type*} [CommRing R] (φ : TwoLocal →+* R) (a : ℕ) (t k : ℤ) :
    (W a t k).eval₂ φ 0 = if k=t then φ (rho a t) else 0 := by
  let H := Polynomial.eval₂RingHom φ (0:R)
  change H (W a t k) = _
  unfold W
  by_cases h : k=t
  · rw [if_pos h,if_pos h,cHat,map_mul,map_prod]
    simp [H]
  · rw [if_neg h,if_neg h]
    simp [H,Polynomial.eval₂_mul]

variable {S V : Type*} [LinearOrder S] [Fintype S]

omit [Fintype S] in
theorem shifted_iff_oriented {a b : ℕ} (mask : MaskFamily a b S) (w : Fin a → S)
    (m l : ℕ) (h : m≤b) (hL : 2*l=2^a) (t : ℕ)
    (r s : Wire w m b l) :
    shifted mask w m l h hL t r = some s ↔
      (oriented mask w m l h hL r).1 = (oriented mask w m l h hL s).1 ∧
      (oriented mask w m l h hL r).2.val+t = (oriented mask w m l h hL s).2.val := by
  constructor
  · exact exact_shift mask w m l h hL t r s
  · intro hs
    let e := placement mask w m l h hL
    have hlt : (e r).2.val+t<2^a :=
      hs.2.symm ▸ (e s).2.isLt
    change (if hh : (e r).2.val+t<2^a then
      some (e.symm ((e r).1,⟨(e r).2.val+t,hh⟩)) else none) = some s
    rw [dif_pos hlt]
    apply congrArg some
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext hs.1 (Fin.ext hs.2)

theorem centre_in_grid (m : ℕ) (i : Fin (m+1)) :
    (index m i : ℤ) ∈ grid (a m) := by
  rw [mem_grid]
  refine ⟨(neg_nonpos.mpr (pow₂_pos _).le).trans (by positivity),?_⟩
  unfold pow₂
  exact_mod_cast (address_index m i).2.2.2

theorem rho_eq_scalar (m : ℕ) (i : Fin (m+1)) :
    rho (a m) (index m i : ℤ) = J6NativeHeightDyadic.scalar m i := by
  apply twoLocalRat_injective
  (rw [rho_rat (centre_in_grid m i),J6NativeHeightDerivative.source_scalar_eq_actual_mesh]; rfl)

set_option maxHeartbeats 2500000 in
theorem mesh_kernel_at_zero
    (f : ℤ[X]) (ell p m l q : ℕ) (T : Plant V m q)
    (w : Fin (a m) → S) (mask : MaskFamily (a m) (K m) S)
    (hm : m≤K m) (hL : 2*l=L m) (hS : Fintype.card S=64)
    (i : Fin (m+1)) (r s : Wire w m (K m) l) :
    finiteEntry p f ell (parentAtlas (rootPacking m l q T w mask hm hL hS)) (index m i : ℤ) 0 r s =
      if shiftAt m l mask w hm hL i r=some s then
        J6ZeroTransport.reduceAt p (box_two_nil p f ell) (J6NativeHeightDyadic.scalar m i)
      else 0 := by
  let P := rootPacking m l q T w mask hm hL hS
  let atlas := parentAtlas P
  have hp (u : Wire w m (K m) l) :
      atlas.page u = (oriented mask w m l hm hL u).1 := rfl
  have hi (u : Wire w m (K m) l) :
      atlas.index u = ((oriented mask w m l hm hL u).2.val:ℤ) := rfl
  have hs : shifted mask w m l hm hL (index m i) r=some s ↔
      atlas.page r=atlas.page s ∧ atlas.index s-atlas.index r=(index m i:ℤ) := by
    rw [hp r,hp s,hi r,hi s]
    refine (shifted_iff_oriented mask w m l hm hL (index m i) r s).trans ?_
    exact and_congr_right (fun _ => by omega)
  change finiteEntry p f ell atlas (index m i : ℤ) 0 r s = _
  rw [finiteEntry,W_eval_zero,rho_eq_scalar,shiftAt]
  by_cases h : atlas.page r=atlas.page s <;> simp [h,hs]

#print axioms W_eval_zero
#print axioms shifted_iff_oriented
#print axioms centre_in_grid
#print axioms rho_eq_scalar
#print axioms mesh_kernel_at_zero
end
end J6R15PlantedIdentity
