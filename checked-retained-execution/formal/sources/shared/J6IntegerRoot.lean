import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-! A computable signed odd-root routine, using exactly one power comparison
per bit of a public root-length cap. No uncharged integer-root oracle. -/
namespace J6IntegerRoot

def recoverNat (f : ℕ → ℕ) (a : ℕ) : ℕ → ℕ → ℕ × ℕ
  | 0, l => (l,0)
  | b+1, l =>
      let k := l+2^b
      let u := recoverNat f a b (if f k ≤ a then k else l)
      (u.1,u.2+1)

theorem recoverNat_steps (f : ℕ → ℕ) (a b l : ℕ) :
    (recoverNat f a b l).2 = b := by
  induction b generalizing l with
  | zero => rfl
  | succ b ih => simp only [recoverNat,ih]

theorem recoverNat_exact (f : ℕ → ℕ) (hf : StrictMono f) (x b l : ℕ)
    (hlo : l ≤ x) (hhi : x < l+2^b) :
    (recoverNat f (f x) b l).1 = x := by
  induction b generalizing l with
  | zero =>
    simp only [pow_zero] at hhi
    change l = x
    omega
  | succ b ih =>
    have hh := hhi
    rw [pow_succ] at hh
    let k := l+2^b
    change (recoverNat f (f x) b (if f k ≤ f x then k else l)).1=x
    by_cases h : k ≤ x
    · rw [if_pos (hf.monotone h)]
      exact ih k h (by dsimp [k]; omega)
    · have hn : ¬ f k ≤ f x := not_le_of_gt (hf (by omega))
      rw [if_neg hn]
      exact ih l hlo (by dsimp [k] at h; omega)

def signed (b e : ℕ) (a : ℤ) : ℤ × ℕ :=
  let v := recoverNat (fun x => x^e) a.natAbs b 0
  (if a < 0 then -(v.1:ℤ) else v.1, v.2)

theorem signed_steps (b e : ℕ) (a : ℤ) : (signed b e a).2 = b :=
  recoverNat_steps _ _ _ _

theorem signed_exact (b e : ℕ) (a : ℤ) (he : Odd e) (h : a.natAbs < 2^b) :
    (signed b e (a^e)).1 = a := by
  have hp : e ≠ 0 := by obtain ⟨j,hj⟩ := he; omega
  have hnat : StrictMono (fun x : ℕ => x^e) := by
    intro x y hxy
    have hxy' : (x:ℤ) < (y:ℤ) := by exact_mod_cast hxy
    have hm : (x:ℤ)^e < (y:ℤ)^e := (he.strictMono_pow (R:=ℤ)) hxy'
    change x^e < y^e
    exact_mod_cast hm
  rw [signed,Int.natAbs_pow,recoverNat_exact _ hnat _ _ _ (Nat.zero_le _) (by simpa)]
  have hsign : a^e < 0 ↔ a < 0 := by
    simpa [zero_pow hp] using (he.strictMono_pow (R:=ℤ)).lt_iff_lt (a:=a) (b:=0)
  rw [if_congr hsign rfl rfl]
  by_cases hn : a < 0
  · rw [if_pos hn]
    omega
  · rw [if_neg hn]
    omega

#print axioms recoverNat_steps
#print axioms recoverNat_exact
#print axioms signed_steps
#print axioms signed_exact
end J6IntegerRoot