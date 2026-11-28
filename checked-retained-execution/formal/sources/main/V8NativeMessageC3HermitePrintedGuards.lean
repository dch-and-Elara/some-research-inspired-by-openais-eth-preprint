import V8NativeMessageC3HermiteMargin
import Mathlib.Data.Nat.Sqrt

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5400000

/-! The full MAIN parameter guard implies the explicit D threshold used
above. The checked original inequality 6R≤Q is essential to this
particular deduction; it is not an assumption on a retuned layout. -/
namespace V8NativeMessage.C3.Hermite.Native
open scoped Classical
open V8PooledMenu.FiveCopy V8PooledRange
open RawMain Canonical
noncomputable section

def ceilSqrt (n : ℕ) : ℕ := if n=0 then 0 else (n-1).sqrt+1

theorem ceilSqrt_le_iff (n k : ℕ) : ceilSqrt n≤k ↔ n≤k^2 := by
  by_cases h : n=0
  · simp [ceilSqrt,h]
  · rw [ceilSqrt,if_neg h,show (n-1).sqrt+1=Nat.succ (n-1).sqrt by rfl,
      Nat.succ_le_iff,Nat.sqrt_lt']
    omega

theorem le_ceilSqrt_sq (n : ℕ) : n≤(ceilSqrt n)^2 := (ceilSqrt_le_iff _ _).mp le_rfl

def sourceR (V : Type) [Fintype V] (β : ℕ) := (β+3)*ceilSqrt (mainLambda V)

theorem source_rootU_le_wireSize (V : Type) [Fintype V] : rootU V≤wireSize V := by
  have hs : rootSize V≤wireSize V := by
    unfold rootSize wireSize
    have hh := Nat.div_le_self (25*Fintype.card V) 2
    omega
  have hp : ∀ n : ℕ, n≤2^n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hpos : 0<(2:ℕ)^n := by positivity
      rw [pow_succ]
      omega
  exact (Nat.div_le_self _ _).trans
    ((Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr (hs.trans (hp (wireSize V))))

variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ]
  {G : Graph V E} {r : ThreePorts G} (F : FiveFile (Γ:=Γ) G r)

theorem source_Q_128_le_lambda (hQ : F.layout.Q=sourceQ V) : 128*F.layout.Q≤mainLambda V := by
  let nu := mainNu V
  let lam := mainLambda V
  let Q := F.layout.Q
  have qpos : 0<Q := F.layout.positive_degree.trans F.layout.degree_lt_nodes
  have he : Q=lam/(128*nu) := hQ
  have hp : 0<nu := by
    by_contra! hh
    rw [Nat.eq_zero_of_le_zero hh,Nat.mul_zero,Nat.div_zero] at he
    omega
  have hl : 128≤128*nu := by
    simpa only [Nat.mul_one] using (Nat.mul_le_mul_left 128 (Nat.succ_le_of_lt hp))
  have hr : (128*nu)*Q≤lam := by
    rw [he,mul_comm]
    exact Nat.div_mul_le_self _ _
  exact (Nat.mul_le_mul_right Q hl).trans hr

theorem source_guards_force_large
    (hQ : F.layout.Q=sourceQ V) {β : ℕ} (hβ : 1≤β)
    (hR : F.layout.R=sourceR V β) (h6 : 6*F.layout.R≤F.layout.Q) :
    15≤rootU V := by
  let n := mainLambda V
  let k := ceilSqrt n
  have hQ128 : 128*F.layout.Q≤n := source_Q_128_le_lambda F hQ
  have hQpos : 0<F.layout.Q := F.layout.positive_degree.trans F.layout.degree_lt_nodes
  have hn : 0<n := by omega
  have hsq : n≤k*k := by simpa only [pow_two] using le_ceilSqrt_sq n
  have hk : 0<k := by
    by_contra! hh
    rw [Nat.eq_zero_of_le_zero hh,Nat.zero_mul] at hsq
    omega
  have hR4 : 4*k≤F.layout.R := by
    rw [hR]
    exact Nat.mul_le_mul_right k (by omega)
  have h3072 : 3072*k≤n := by omega
  have hlower : 3072≤k := Nat.le_of_mul_le_mul_right (h3072.trans hsq) hk
  have hN : 15*(128*1024)≤n :=
    (show 15*(128*1024)≤3072*3072 by decide).trans
      ((Nat.mul_le_mul_left _ hlower).trans h3072)
  have ht : n≤Nat.clog 2 (rootSize V) :=
    Nat.clog_mono_right _ (actual_variable_vs_root G r)
  exact (Nat.le_div_iff_mul_le (by decide)).mpr (hN.trans ht)

theorem ordinary_main_full_printed_guards
    (hQ : F.layout.Q=sourceQ V) {β : ℕ} (hβ : 1≤β)
    (hR : F.layout.R=sourceR V β) (h6 : 6*F.layout.R≤F.layout.Q) (t : Site V) :
    ordinaryMainLoss F ≤ 2*(printedH V*nodeD t)+4*(wireSize V*(rootA V+1)) :=
  ordinary_main_printed_margin F hQ (source_guards_force_large F hQ hβ hR h6)
    (source_rootU_le_wireSize V) t

#print axioms ceilSqrt_le_iff
#print axioms le_ceilSqrt_sq
#print axioms source_rootU_le_wireSize
#print axioms source_Q_128_le_lambda
#print axioms source_guards_force_large
#print axioms ordinary_main_full_printed_guards
end
end V8NativeMessage.C3.Hermite.Native
