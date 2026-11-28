import V8CapacityResidueCounts
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! A faithful finite base-q digit chart over a principal local residue
quotient, with the exact residue-class correspondence modulo π^u. No Ghost
digit or characteristic-zero assumption enters the chart. -/
namespace V8CapacityDigits
open scoped Classical
variable {O : Type*} [CommRing O]
variable {π : O} {q : ℕ} {hq : 0<q}

structure Digits (π : O) (q : ℕ) where
  d : Fin q → O
  covers : ∀ x : O, ∃ i : Fin q, ∃ y : O, x=d i+π*y
  sep : ∀ i j : Fin q, π∣d i-d j → i=j

def first (hq : 0<q) (n : ℕ) : Fin q := ⟨n%q,Nat.mod_lt _ hq⟩

def prefixDigits (D : Digits π q) (hq : 0<q) : ℕ → ℕ → O
  | 0, _ => 0
  | u+1,n => D.d (first hq n)+π*prefixDigits D hq u (n/q)

theorem mod_pair_iff (n q D i m : ℕ) (hq : 0<q) (hi : i<q) :
    n%(q*D)=i+q*m ↔ n%q=i ∧ (n/q)%D=m := by
  constructor
  · intro h
    have h₁ := congrArg (fun x : ℕ => x%q) h
    have h₂ := congrArg (fun x : ℕ => x/q) h
    simp only [Nat.mod_mul_right_mod,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hi] at h₁
    simp only [Nat.mod_mul_right_div_self,Nat.add_mul_div_left _ _ hq,Nat.div_eq_of_lt hi,zero_add] at h₂
    exact ⟨h₁,h₂⟩
  · rintro ⟨h₁,h₂⟩
    rw [Nat.mod_mul,h₁,h₂]

theorem partial_compat (D : Digits π q) (hq : 0<q) (u v : ℕ) (h : u≤v) (n : ℕ) :
    π^u ∣ prefixDigits D hq v n-prefixDigits D hq u n := by
  induction u generalizing v n with
  | zero => simp
  | succ u ih =>
    cases v with
    | zero => omega
    | succ v =>
      rw [prefixDigits,prefixDigits,pow_succ']
      have hh : D.d (first hq n)+π*prefixDigits D hq v (n/q)-
        (D.d (first hq n)+π*prefixDigits D hq u (n/q)) =
        π*(prefixDigits D hq v (n/q)-prefixDigits D hq u (n/q)) := by ring
      rw [hh]
      exact mul_dvd_mul_left _ (ih v (by omega) _)

variable [IsDomain O]

/-- For every x, all digit nodes congruent to x at depth u form exactly
one ordinary residue class modulo q^u. The representative need not be
the zero residue, and the leading digits are selected before enumeration. -/
theorem partial_class (D : Digits π q) (hq : 0<q) (hπ : π≠0) (u : ℕ) (x : O) :
    ∃ r : Fin (q^u), ∀ n, π^u∣x-prefixDigits D hq u n ↔ n%(q^u)=r.val := by
  induction u generalizing x with
  | zero =>
    refine ⟨⟨0,by simp⟩,?_⟩
    intro n
    simp only [pow_zero,one_dvd,true_iff]
    exact Nat.mod_one n
  | succ u ih =>
    obtain ⟨i,y,rfl⟩ := D.covers x
    obtain ⟨m,hm⟩ := ih y
    let r := i.val+q*m.val
    have hr : r<q^(u+1) := by
      rw [pow_succ']
      calc
        r < q*(m.val+1) := by dsimp [r]; rw [Nat.mul_succ]; omega
        _ ≤ q*q^u := Nat.mul_le_mul_left q m.isLt
    refine ⟨⟨r,hr⟩,fun n => ?_⟩
    have hnat : n%q^(u+1)=r ↔ n%q=i.val ∧ (n/q)%q^u=m.val := by
      rw [pow_succ']
      exact mod_pair_iff n q (q^u) i.val m.val hq i.isLt
    rw [hnat]
    constructor
    · intro hd
      have hall : π∣ D.d i+π*y-prefixDigits D hq (u+1) n := by
        apply dvd_trans _ hd
        simpa only [pow_one] using pow_dvd_pow π (show 1≤u+1 by omega)
      rw [prefixDigits] at hall
      have hsmall : π∣ D.d i-D.d (first hq n) := by
        have hp := dvd_sub hall (dvd_mul_right π (y-prefixDigits D hq u (n/q)))
        convert hp using 1; ring
      have hs := D.sep i (first hq n) hsmall
      refine ⟨(congrArg Fin.val hs).symm,?_⟩
      have hb : π*(π^u) ∣ π*(y-prefixDigits D hq u (n/q)) := by
        rw [pow_succ',prefixDigits,← hs] at hd
        convert hd using 1; ring
      exact (hm _).mp ((mul_dvd_mul_iff_left hπ).mp hb)
    · rintro ⟨hn,hr⟩
      have hs : first hq n=i := Fin.ext hn
      have hb := mul_dvd_mul_left π ((hm _).mpr hr)
      rw [pow_succ',prefixDigits,hs]
      convert hb using 1; ring

variable [IsLocalRing O]

def fromLocalResidue (π : O) (hπ : IsLocalRing.maximalIdeal O = Ideal.span ({π}:Set O))
    (e : Fin q ≃ IsLocalRing.ResidueField O)
    (d : IsLocalRing.ResidueField O → O)
    (hd : Function.RightInverse d (IsLocalRing.residue O)) : Digits π q where
  d := d ∘ e
  covers x := by
    let a := e.symm (IsLocalRing.residue O x)
    have hz : IsLocalRing.residue O (x-d (e a))=0 := by
      rw [map_sub,hd,show e a=IsLocalRing.residue O x from e.apply_symm_apply _,sub_self]
    have hD : π∣x-d (e a) := by
      have hz' : x-d (e a)∈IsLocalRing.maximalIdeal O := (IsLocalRing.residue_eq_zero_iff _).mp hz
      rw [hπ,Ideal.mem_span_singleton] at hz'
      exact hz'
    obtain ⟨y,hy⟩ := hD
    exact ⟨a,y,by change x=d (e a)+π*y; rw [← hy]; ring⟩
  sep a b h := by
    apply e.injective
    have hD : d (e a)-d (e b)∈IsLocalRing.maximalIdeal O := by
      rw [hπ,Ideal.mem_span_singleton]
      exact h
    have hz := (IsLocalRing.residue_eq_zero_iff _).mpr hD
    rw [map_sub,hd,hd] at hz
    exact sub_eq_zero.mp hz

#print axioms mod_pair_iff
#print axioms partial_compat
#print axioms partial_class
#print axioms fromLocalResidue
end V8CapacityDigits
