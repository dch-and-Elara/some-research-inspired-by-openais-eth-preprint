import J9R14LowPrecisionSlots
import J6R10RowAffine

/-!
# Instantiation by real native local and crossing factors

This is the actual nonzero-centre row/moment interface of Appendix D.
No row/kernel equality or support budget is supplied by the caller.
The source's cheaper menu weight b+1 is not changed; we extract the
stronger tariff a+1-i+b from the already implemented native factor.
-/

namespace J9R14LowPrecisionNative
open scoped Polynomial BigOperators Classical
open Polynomial DenominatorBudget P11FullPacking J6R9PacketScopes J6R9PacketChild J6R9PacketTiles
open J6R9PacketCoeff J9R14LowPrecisionGeometry J9R14LowPrecisionKernel
open J9R14LowPrecisionSlots J9R14LowPrecisionTiedCube J9R14LowPrecisionColumn

noncomputable section
variable {S R Q A : Type*} [LinearOrder S] [Fintype R] [Fintype Q]
variable {a b : ℕ}
variable (ρ : R→Physical a b S) (κ : Q→Physical a b S) (mask : MaskFamily a b S) (i : Fin a)
variable {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val) (p : ℕ)

def tariff (m : Mode i p mask) : ℕ := a+1-i.val+m.order.val

def kernel (r : R) (m : Mode i p mask) : TwoLocal[X] :=
  if h : rowBlock mask i (ρ r)=target mask i m then
    kernelPoly a p (crossingOf ht hv (targeted_row_bit mask i (ρ r) m h)) m.order.val
  else 0

def momentCoeff (m : Mode i p mask) (q : Q) : TwoLocal :=
  if q ∈ columns (fun q => (κ q).1) (fun q => (κ q).2.val) i.val m.page m.tile.val
  then (coord i.val (κ q).2.val:TwoLocal)^m.order.val else 0

variable {K : Type*} [CommRing K] (hnil : (2:K)^p=0) (z : K)

set_option linter.unusedSectionVars false in
theorem moment_is_native (m : Mode i p mask) (X : Q→Bool) :
    (∑ q : Q, C (momentCoeff κ mask i p m q)*bitC (X q)).eval₂ (J6ZeroTransport.reduceAt p hnil) (2*z) =
      moment κ mask i m (fun q => X q.val) := by
  rw [moment_exact,Polynomial.eval₂_finset_sum]
  unfold L columns
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : (κ q).1=m.page ∧ tile i.val (κ q).2.val=m.tile.val
  · cases X q <;> simp [momentCoeff,columns,hq,bitC,bit]
    let E := Polynomial.eval₂RingHom (J6ZeroTransport.reduceAt p hnil) (2*z)
    change E ((coord i.val (κ q).2.val:TwoLocal[X])^m.order.val) = _
    rw [map_pow,map_natCast]
  · simp [momentCoeff,columns,hq]

set_option linter.unusedSectionVars false in
theorem kernel_is_native (r : R) (m : Mode i p mask) :
    (2:K)^(tariff mask i p m)*z*
      (kernel ρ mask i ht hv p r m).eval₂ (J6ZeroTransport.reduceAt p hnil) (2*z) =
      (2:K)^(m.order.val+1)*crossNorm mask i ht hv p hnil z (ρ r) m := by
  by_cases hm : rowBlock mask i (ρ r)=target mask i m
  · rw [kernel,dif_pos hm,on_target_exact mask i ht hv p hnil z (ρ r) m hm,
      mode_is_public_poly a p m.order.val hnil i.isLt.le]
    rfl
  · simp [kernel,hm,off_target mask i ht hv p hnil z (ρ r) m hm]

def actualLeg (Y : R→Bool) (X : Q→Bool) (r : R) (m : Option (Mode i p mask)) : K :=
  J6ActiveAllocation.scaled (J6R10RowAffine.weight i p mask)
    (J6SourceMoment.insert
      (fun r => row ρ κ mask i ht hv p hnil z r
        ((fun q => Y q.val),(fun q => X q.val)))
      (fun m => moment κ mask i m (fun q => X q.val))) r m

def take (r : R) (q : Q) : Prop := colGroup mask i (κ q)=rowGroup mask i (ρ r)

set_option linter.unusedSectionVars false in
theorem actual_leg_eval (Y : R→Bool) (X : Q→Bool) (α : R→Option (Mode i p mask)) (r : R) :
    actualLeg ρ κ mask i ht hv p hnil z Y X r (α r) =
      ((2:K)^(J6ActiveAllocation.cost (tariff mask i p) (α r)) * z^(allowance α r)) *
      (leg (nativeSeats ρ κ) t a (take ρ κ mask i) (kernel ρ mask i ht hv p)
        (momentCoeff κ mask i p) Y α r X).eval₂ (J6ZeroTransport.reduceAt p hnil) (2*z) := by
  have hs : (J6ZeroTransport.reduceAt p hnil)
      (LiteralPortCompiler.slope (R:=TwoLocal) (Y r)) =
      LiteralPortCompiler.slope (R:=K) (Y r) := by
    cases Y r <;> simp [LiteralPortCompiler.slope]
  cases hn : α r with
  | none =>
    simp only [actualLeg,J6ActiveAllocation.scaled,J6ActiveAllocation.cost,J6SourceMoment.insert,
      hn,Option.elim'_none,allowance,Option.isSome_none,Bool.false_eq_true,if_false,
      pow_zero,one_mul,mul_one,row,leg]
    have E := rowPoly_is_native ρ κ mask i t r p hnil z X
    have hbit (q : Q) : bitC (X q) = C (bit TwoLocal (X q)) := by
      cases X q <;> simp [bitC,bit]
    simp_rw [hbit]
    change _ = (LiteralPortCompiler.affine (Y r) (rowPoly ρ κ mask i t r X)).eval₂
      (J6ZeroTransport.reduceAt p hnil) (2*z)
    cases Y r <;> simp [LiteralPortCompiler.affine,Polynomial.eval₂_sub,E]
  | some m =>
    simp only [actualLeg,J6ActiveAllocation.scaled,J6ActiveAllocation.cost,J6SourceMoment.insert,
      hn,Option.elim'_some,allowance,Option.isSome_some,if_true,pow_one,row,leg,
      Polynomial.eval₂_mul,Polynomial.eval₂_C,hs,J6R10RowAffine.weight]
    rw [moment_is_native κ mask i p hnil z m X]
    have H := kernel_is_native ρ mask i ht hv p hnil z r m
    linear_combination (LiteralPortCompiler.slope (R:=K) (Y r) *
      moment κ mask i m (fun q => X q.val))*(-H)

variable [Fintype (Mode i p mask)]
set_option linter.unusedSectionVars false in
theorem tariff_count (α : R→Option (Mode i p mask)) :
    (∑ r : R, J6ActiveAllocation.cost (tariff mask i p) (α r)) =
      ∑ m : Mode i p mask, tariff mask i p m * (∑ r : R, LiteralPortCompiler.exponent (α r)) m := by
  simp only [Finsupp.finset_sum_apply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  cases α r with
  | none => simp [J6ActiveAllocation.cost,LiteralPortCompiler.exponent]
  | some m =>
    simp [J6ActiveAllocation.cost,LiteralPortCompiler.exponent,Finsupp.single_apply]

#print axioms moment_is_native
#print axioms kernel_is_native
#print axioms actual_leg_eval
#print axioms tariff_count

end
end J9R14LowPrecisionNative
