import V8NativeMessageN5Trace
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option warningAsError true

/-! Exact finite N5 counting, including the unmaterialized single
multiplication variant. The sole algebraic premise is the summed
rank bound, not a claim that every term attains its own ceiling. -/
namespace V8NativeMessage.N5
open scoped Classical BigOperators

variable {H : Type*} [Fintype H] {r κ : H→ℕ} {b : ∀ h,Fin (r h)→ℕ}

theorem work_power {m width T κmax rmax power : ℕ}
    (rank : 2^m≤∑ h, κ h*∏ g, b h g)
    (k : Fintype.card H≤(width*T)^power)
    (points : ∀ h g, b h g≤width*T)
    (jet : ∀ h, κ h≤κmax) (groups : ∀ h, r h≤rmax) (hpow : 0<power) :
    2^m≤κmax*(width*T)^(rmax+power) := by
  have basePos : 0<width*T := by
    by_contra! h
    have hz : width*T=0 := Nat.eq_zero_of_le_zero h
    rw [hz,zero_pow hpow.ne'] at k
    have hH := Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_le_zero k)
    letI := hH
    have hzero : (∑ h, κ h*∏ g, b h g)=0 := Finset.sum_eq_zero fun h _ => isEmptyElim h
    rw [hzero] at rank
    exact (Nat.ne_zero_of_lt (pow_pos (by decide : 0<(2:ℕ)) m)) (Nat.eq_zero_of_le_zero rank)
  apply rank.trans
  calc
    _ ≤ ∑ h : H,κmax*(width*T)^rmax := by
      apply Finset.sum_le_sum
      intro h _
      apply Nat.mul_le_mul (jet h)
      calc
        _ ≤ ∏ _g : Fin (r h),width*T :=
          Finset.prod_le_prod' (fun g _=>points h g)
        _ = (width*T)^(r h) := by simp
        _ ≤ _ := Nat.pow_le_pow_right basePos (groups h)
    _ = Fintype.card H*(κmax*(width*T)^rmax) := by simp
    _ ≤ (width*T)^power*(κmax*(width*T)^rmax) := Nat.mul_le_mul_right _ k
    _ = _ := by rw [pow_add]; ac_rfl

variable {L V : Type*} {width : ℕ}

structure Roster (I : Type*) (t : Trace L V width) where
  key : I→L
  unique : Function.Injective key
  value : I→V
  delivered : ∀ i, Provides t (key i) (value i)

theorem Roster.card_le {I : Type*} [Fintype I] {t : Trace L V width} (r : Roster I t) :
    Fintype.card I≤width*time t :=
  designated_le_work t r.key r.unique r.value r.delivered

theorem paid_explicit {t : Trace L V width} {m κmax rmax : ℕ}
    (rank : 2^m≤∑ h, κ h*∏ g, b h g)
    (cross : Roster H t) (privatePoints : ∀ h g, Roster (Fin (b h g)) t)
    (jet : ∀ h, κ h≤κmax) (groups : ∀ h, r h≤rmax) :
    2^m≤κmax*(width*time t)^(rmax+1) := by
  exact work_power rank (by simpa only [pow_one] using cross.card_le)
    (fun h g=>by simpa only [Fintype.card_fin] using (privatePoints h g).card_le)
    jet groups Nat.one_pos

/-- A single product is expanded algebraically, not charged per pair.
After collecting repeats or dropping zero terms, its distinct
cross terms inject into the original pair set. -/
theorem paid_single_symbolic {I J : Type*} [Fintype I] [Fintype J]
    {t : Trace L V width} {m κmax rmax : ℕ}
    (rank : 2^m≤∑ h, κ h*∏ g, b h g)
    (assignment : H↪I×J) (left : Roster I t) (right : Roster J t)
    (privatePoints : ∀ h g, Roster (Fin (b h g)) t)
    (jet : ∀ h, κ h≤κmax) (groups : ∀ h, r h≤rmax) :
    2^m≤κmax*(width*time t)^(rmax+2) := by
  have hK : Fintype.card H≤(width*time t)^2 := by
    calc
      _ ≤ Fintype.card (I×J) := Fintype.card_le_of_injective _ assignment.injective
      _ = Fintype.card I*Fintype.card J := Fintype.card_prod _ _
      _ ≤ (width*time t)*(width*time t) := Nat.mul_le_mul left.card_le right.card_le
      _ = _ := (pow_two _).symm
  exact work_power rank hK
    (fun h g=>by simpa only [Fintype.card_fin] using (privatePoints h g).card_le)
    jet groups (by decide)

/-- The N5 logarithmic form follows exactly; no special convention is
needed at width, time or maximum order zero, since the power bound
excludes those cases for every rank target. -/
theorem log_of_work_power (m width T κmax r : ℕ) (hr : 0<r)
    (hp : 2^m≤κmax*(width*T)^r) :
    ((m:ℝ)-Real.logb 2 κmax)/r-Real.logb 2 width≤Real.logb 2 T := by
  have hpos := (pow_pos (by decide : 0<(2:ℕ)) m).trans_le hp
  have hk : 0<κmax := Nat.pos_of_ne_zero (by intro e; simp [e] at hpos)
  have hw : 0<width := Nat.pos_of_ne_zero (by intro e; simp [e,zero_pow hr.ne'] at hpos)
  have ht : 0<T := Nat.pos_of_ne_zero (by intro e; simp [e,zero_pow hr.ne'] at hpos)
  have kr : 0<(κmax:ℝ) := by exact_mod_cast hk
  have wr : 0<(width:ℝ) := by exact_mod_cast hw
  have tr : 0<(T:ℝ) := by exact_mod_cast ht
  have rr : 0<(r:ℝ) := by exact_mod_cast hr
  have hp' : (2:ℝ)^m≤(κmax:ℝ)*((width:ℝ)*(T:ℝ))^r := by exact_mod_cast hp
  have hlog := Real.logb_le_logb_of_le (b:=2) (by norm_num) (pow_pos (by norm_num) m) hp'
  simp only [Real.logb_mul kr.ne' (pow_pos (mul_pos wr tr) r).ne',Real.logb_pow,
    Real.logb_mul wr.ne' tr.ne',Real.logb_self_eq_one (by norm_num : 1<(2:ℝ))
      ,mul_one] at hlog
  apply sub_le_iff_le_add.mpr
  apply (div_le_iff₀ rr).mpr
  nlinarith only [hlog]

#print axioms work_power
#print axioms Roster.card_le
#print axioms paid_explicit
#print axioms paid_single_symbolic
#print axioms log_of_work_power
end V8NativeMessage.N5