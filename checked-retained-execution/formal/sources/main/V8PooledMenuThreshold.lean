import V8PooledMenuDecoder

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

namespace V8PooledMenu
open scoped Classical Polynomial
open Polynomial V8PooledRange V8PooledMenu.FiveCopy

private theorem succ_le_pow2 (n : ℕ) : n+1 ≤ (2:ℕ)^n := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    omega

theorem rootU_fits (V : Type) [Fintype V] : rootU V ≤ wireSize V := by
  have h : Nat.clog 2 (rootSize V) ≤ rootSize V :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
      ((Nat.le_succ _).trans (succ_le_pow2 _))
  exact (Nat.div_le_self _ _).trans (h.trans (by unfold rootSize wireSize; omega))

theorem root_leaf_guard (V : Type) [Fintype V] :
    J9PrintedSchedule.leafThreshold (rootSize V) (Nat.clog 2 (rootSize V)) < wireSize V := by
  let s := rootSize V
  let d := (Nat.clog 2 s).sqrt
  have hs : 2≤s := by dsimp [s,rootSize]; omega
  have hd : 0<d := Nat.sqrt_pos.mpr (Nat.clog_pos (by decide) hs)
  have hh : (s+d-1)/d < s+1 := (Nat.div_lt_iff_lt_mul hd).mpr (by
    calc
      s+d-1 < s+d := by omega
      _ ≤ (s+1)*d := by
        rw [Nat.add_mul,one_mul]
        exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hd) _)
  change (s+d-1)/d < wireSize V
  exact (Nat.le_of_lt_succ hh).trans_lt (by dsimp [s,rootSize,wireSize]; omega)

private theorem coarse_tape_exp {a u : ℕ} (hua : u≤a) (p : Fin u→ℕ)
    (hp : ∀ i, p i≤a+1-i.val) :
    pooledBits a u p < (2:ℕ)^(3*a+3) := by
  have hm : triangle (a+1) ≤ (2:ℕ)^(a+1)*(2:ℕ)^(a+1) := by
    unfold triangle
    exact (Nat.div_le_self _ _).trans
      (Nat.mul_le_mul (Nat.le_of_lt ((Nat.lt_succ_self (a+1)).trans_le (succ_le_pow2 (a+1))))
        (succ_le_pow2 (a+1)))
  calc
    _ < (2*2^a)*triangle (a+1) := pooledBits_strict hua p hp
    _ ≤ (2*2^a)*((2:ℕ)^(a+1)*(2:ℕ)^(a+1)) := Nat.mul_le_mul_left _ hm
    _ = (2:ℕ)^(3*a+3) := by rw [← pow_succ',← pow_add,← pow_add]; congr 1; omega

/-- Exact numeric consequence for every genuinely active printed root
here. It avoids taking any floor/ceil or asymptotic estimate on faith. -/
theorem active_excludes_side_free {V : Type} [Fintype V]
    (hu : 0<rootU V) (L : PublicPrecision V) :
    12*pooledBits (rootA V) (rootU V) L.prec+10 < Fintype.card V := by
  let lam := Nat.clog 2 (rootSize V)
  let a := rootA V
  let B := pooledBits a (rootU V) L.prec
  have hlarge : (128*1024)*rootU V ≤ lam := by
    unfold rootU lam
    simpa only [Nat.mul_comm] using (Nat.div_mul_le_self (Nat.clog 2 (rootSize V)) (128*1024))
  have hA : a=2*rootU V := rfl
  have he : 3*a+3 ≤ lam-10 := by omega
  have hB : B < 2^(lam-10) :=
    (coarse_tape_exp (by omega : rootU V≤a) L.prec L.cap).trans_le
      (Nat.pow_le_pow_right (by decide) he)
  have hs : (2:ℕ)^(lam-1) < rootSize V := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mp
    change lam-1<lam
    omega
  have hpow : (512:ℕ)*2^(lam-10) = 2^(lam-1) := by
    change (2:ℕ)^9 * 2^(lam-10) = _
    rw [← pow_add]
    congr 1
    omega
  have hBS : 512*B < rootSize V :=
    ((Nat.mul_lt_mul_of_pos_left hB (by decide : 0 < (512:ℕ))).trans_eq hpow).trans hs
  have hN : 32<Fintype.card V := by
    by_contra! hn
    have hr : rootSize V ≤ 2^9 := by unfold rootSize; omega
    have hh : lam≤9 := (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr hr
    omega
  change 12*B+10 < Fintype.card V
  unfold rootSize at hBS
  omega

theorem no_menu_only_decoder {k : ℕ} {E : Type} [Fintype E]
    (H : Graph (Deficit k) E) (p : ThreePorts H)
    (P : Packing (Split.graph H p) (Split.ports H p))
    (hu : 0<rootU (Split.V k)) (huM : rootU (Split.V k)≤wireSize (Split.V k))
    (L : PublicPrecision (Split.V k)) {f : ℤ[X]}
    (pr : Probes (Split.V k) f) (hf : f.Monic) (hd : 0<f.natDegree)
    (D : WholeMenu f P hu huM L → ℕ) :
    ¬∀ s, D (nativeMenu P hu huM L pr hf s) = NativeOrigin.originCount (Split.graph H p) (Split.ports H p) s := by
  intro h
  have hb := actual_pooled_decoder H p P hu huM L pr hf hd
    0 (fun _ => Unit) (by intro _; change Fintype.card Unit ≤ 2^0; decide) (fun _ => ())
    (fun x => D x.1) h
  have hc := active_excludes_side_free hu L
  have hb' : ((Fintype.card (Split.V k) : ℚ)-10)/12 ≤
      (pooledBits (rootA (Split.V k)) (rootU (Split.V k)) L.prec : ℚ) := hb
  have hc' : 12*(pooledBits (rootA (Split.V k)) (rootU (Split.V k)) L.prec : ℚ)+10 <
      (Fintype.card (Split.V k) : ℚ) := by exact_mod_cast hc
  linarith only [hb',hc']

#print axioms rootU_fits
#print axioms root_leaf_guard
#print axioms active_excludes_side_free
#print axioms no_menu_only_decoder
end V8PooledMenu
