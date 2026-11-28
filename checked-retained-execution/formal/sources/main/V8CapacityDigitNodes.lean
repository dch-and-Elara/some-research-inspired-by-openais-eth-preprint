import V8CapacityDigitChart

/-! The real finite expansion of an unbounded natural label, and its
congruence classes at every depth. Zero is explicitly the zero digit. -/
namespace V8CapacityDigits
open scoped Classical
variable {O : Type*} [CommRing O] {π : O} {q : ℕ}

theorem partial_next (D : Digits π q) (hq : 0<q) (h0 : D.d ⟨0,hq⟩=0)
    (u n : ℕ) (hn : n<q^u) :
    prefixDigits D hq (u+1) n=prefixDigits D hq u n := by
  induction u generalizing n with
  | zero =>
    have hn0 : n=0 := by simpa using hn
    subst n
    have hf : first hq 0=⟨0,hq⟩ := by apply Fin.ext; exact Nat.zero_mod q
    simp [prefixDigits,hf,h0]
  | succ u ih =>
    have hb : n/q<q^u := Nat.div_lt_of_lt_mul (by simpa only [pow_succ'] using hn)
    change D.d (first hq n)+π*prefixDigits D hq (u+1) (n/q) =
      D.d (first hq n)+π*prefixDigits D hq u (n/q)
    rw [ih _ hb]

theorem partial_more (D : Digits π q) (hq : 0<q) (h0 : D.d ⟨0,hq⟩=0)
    (u v n : ℕ) (hu : u≤v) (hn : n<q^u) :
    prefixDigits D hq v n=prefixDigits D hq u n := by
  obtain ⟨w,rfl⟩ := Nat.exists_eq_add_of_le hu
  induction w with
  | zero => rfl
  | succ w ih =>
    have hb : n<q^(u+w) :=
      hn.trans_le (Nat.pow_le_pow_right hq (Nat.le_add_right u w))
    rw [Nat.add_succ,partial_next D hq h0 _ _ hb,ih (Nat.le_add_right u w)]

theorem successor_le_pow (q : ℕ) (hq : 2≤q) (n : ℕ) : n+1≤q^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    calc
      n+1+1≤2*(n+1) := by omega
      _≤q*q^n := Nat.mul_le_mul hq ih

def node (D : Digits π q) (hq : 0<q) (n : ℕ) : O := prefixDigits D hq (n+1) n

theorem node_compat (D : Digits π q) (hq2 : 2≤q) (hq : 0<q)
    (h0 : D.d ⟨0,hq⟩=0) (u n : ℕ) :
    π^u∣node D hq n-prefixDigits D hq u n := by
  by_cases hu : u≤n+1
  · exact partial_compat D hq u (n+1) hu n
  · have hN : n<q^(n+1) := (Nat.lt_succ_self n).trans_le
      ((Nat.le_succ (n+1)).trans (successor_le_pow q hq2 (n+1)))
    unfold node
    rw [partial_more D hq h0 (n+1) u n (by omega) hN,sub_self]
    exact dvd_zero _

variable [IsDomain O]

theorem node_class (D : Digits π q) (hq2 : 2≤q) (hq : 0<q)
    (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0) (u : ℕ) (x : O) :
    ∃ r : Fin (q^u), ∀ n, π^u∣x-node D hq n ↔ n%q^u=r.val := by
  obtain ⟨r,hr⟩ := partial_class D hq hπ u x
  refine ⟨r,fun n => (Iff.trans ?_ (hr n))⟩
  have hc := node_compat D hq2 hq h0 u n
  constructor
  · intro hx
    have H := dvd_add hx hc
    convert H using 1; ring
  · intro hx
    have H := dvd_sub hx hc
    convert H using 1; ring

theorem node_diff_iff (D : Digits π q) (hq2 : 2≤q) (hq : 0<q)
    (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0) (u n m : ℕ) :
    π^u∣node D hq n-node D hq m ↔ m%q^u=n%q^u := by
  obtain ⟨r,hr⟩ := node_class D hq2 hq h0 hπ u (node D hq n)
  have hn : n%q^u=r.val := (hr n).mp (by simp)
  rw [hr m,hn]

theorem node_injective (D : Digits π q) (hq2 : 2≤q) (hq : 0<q)
    (h0 : D.d ⟨0,hq⟩=0) (hπ : π≠0) : Function.Injective (node D hq) := by
  intro n m h
  let u := max n m+1
  have hh : max n m<q^u := (Nat.lt_succ_self _).trans_le
    ((Nat.le_succ u).trans (successor_le_pow q hq2 u))
  have hz := (node_diff_iff D hq2 hq h0 hπ u n m).mp (by rw [h,sub_self]; exact dvd_zero _)
  rw [Nat.mod_eq_of_lt ((le_max_right n m).trans_lt hh),
    Nat.mod_eq_of_lt ((le_max_left n m).trans_lt hh)] at hz
  exact hz.symm

#print axioms partial_next
#print axioms partial_more
#print axioms successor_le_pow
#print axioms node_compat
#print axioms node_class
#print axioms node_diff_iff
#print axioms node_injective
end V8CapacityDigits
