import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Tactic

/-! §7 independent-error precision for a fixed finite matrix of a
decoder. Orders belong to every node; the slot type has no coordinates
at any omitted node. Endpoint sharpness is isolated as a separate
arithmetic obligation, not assumed for the final native proof. -/
namespace Paper5.P3
open scoped BigOperators

variable {K : Type*} [Field K] {T : Type*} [Fintype T]

def InLattice (O : Subring K) (s : K) (x : K) : Prop :=
  ∃ u : O, x = s * (u : K)

theorem lattice_zero (O : Subring K) (s : K) : InLattice O s 0 :=
  ⟨0,by simp⟩

theorem lattice_add (O : Subring K) (s : K) {x y : K}
    (hx : InLattice O s x) (hy : InLattice O s y) : InLattice O s (x+y) := by
  obtain ⟨u,rfl⟩ := hx
  obtain ⟨v,rfl⟩ := hy
  exact ⟨u+v,by simp only [Subring.coe_add,mul_add]⟩

theorem lattice_mul_integral (O : Subring K) (s : K) {x : K}
    (hx : InLattice O s x) (u : O) : InLattice O s (x*(u:K)) := by
  obtain ⟨v,rfl⟩ := hx
  exact ⟨v*u,by simp only [Subring.coe_mul,mul_assoc]⟩

theorem lattice_sum {I : Type*} (O : Subring K) (s : K) (A : Finset I) (x : I→K)
    (h : ∀ i∈A, InLattice O s (x i)) : InLattice O s (∑ i∈A,x i) := by
  classical
  revert h
  induction A using Finset.induction_on with
  | empty => intro _; simpa using lattice_zero O s
  | insert i A hi ih =>
    intro h
    rw [Finset.sum_insert hi]
    exact lattice_add O s (h i (Finset.mem_insert_self i A))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem lattice_rescale_iff (O : Subring K) (s : Kˣ) (x : K) :
    InLattice O (s:K) x ↔ x/(s:K) ∈ O := by
  constructor
  · rintro ⟨a,rfl⟩
    rw [mul_comm,mul_div_cancel_right₀ _ (Units.ne_zero s)]
    exact a.property
  · intro h
    refine ⟨⟨x/(s:K),h⟩,?_⟩
    change x = (s:K)*(x/(s:K))
    rw [mul_comm,div_mul_cancel₀ _ (Units.ne_zero s)]

abbrev Slot (q : T→ℕ) := Σ t : T, Fin (q t)

def Certified (O : Subring K) (q : T→ℕ) (b : ℕ) (entry : Slot q→Fin b→Fin b→K)
    (a : T→K) (s : K) : Prop :=
  ∀ (e : Slot q→O) (i j : Fin b), InLattice O s (∑ x, entry x i j * a x.1 * (e x:K))

omit [Fintype T] in
theorem exact_scaled_generator (O : Subring K) (π : Kˣ) (hm : ∀ n : ℤ, (↑(π^n):K)∈O ↔ 0≤n)
    (P p c : ℤ) (w : Oˣ) :
    InLattice O (↑(π^p):K) ((↑(π^P):K)*(↑(π^c):K)*((w:O):K)) ↔ 0≤P+c-p := by
  rw [lattice_rescale_iff]
  have h (x : K) : x*((w:O):K) ∈ O ↔ x∈O := by
    constructor
    · intro hx
      have hh := O.mul_mem hx (show (((w⁻¹ : Oˣ):O):K)∈O from Subtype.property _)
      have he : x*((w:O):K)*(((w⁻¹ : Oˣ):O):K)=x := by
        rw [mul_assoc,←Subring.coe_mul,Units.mul_inv,Subring.coe_one,mul_one]
      rwa [he] at hh
    · intro hx
      exact O.mul_mem hx (Subtype.property _)
  have he : (↑(π^P):K)*(↑(π^c):K)*((w:O):K)/(↑(π^p):K) =
      (↑(π^(P+c-p)):K)*((w:O):K) := by
    rw [sub_eq_add_neg,zpow_add,zpow_add,zpow_neg]
    simp only [Units.val_mul,Units.val_inv_eq_inv_val,div_eq_mul_inv]
    ac_rfl
  rw [he,h,hm]

theorem independent_entries_iff (O : Subring K) (q : T→ℕ) (b : ℕ)
    (entry : Slot q→Fin b→Fin b→K) (a : T→K) (s : K) :
    Certified O q b entry a s ↔
      ∀ (x : Slot q) (i j : Fin b), InLattice O s (entry x i j * a x.1) := by
  classical
  constructor
  · intro H x i j
    have hx := H (fun y => if y=x then 1 else 0) i j
    simpa [apply_ite,Finset.sum_ite_eq'] using hx
  · intro H e i j
    exact lattice_sum O s Finset.univ _ fun x _ => lattice_mul_integral O s (H x i j) (e x)

/-- Each node has a uniform denominator envelope and attains it in a
single input/output entry, up to a unit of the ground ring. Then the
independent-error criterion tests one exact generator per retained node. -/
theorem attained_envelope_iff (O : Subring K) (q : T→ℕ) (b : ℕ)
    (entry : Slot q→Fin b→Fin b→K) (a M : T→K) (s : K)
    (bound : ∀ (x : Slot q) (i j : Fin b), InLattice O (M x.1) (entry x i j))
    (attain : ∀ t, 0<q t → ∃ (r : Fin (q t)) (i j : Fin b) (w : Oˣ),
      entry ⟨t,r⟩ i j = M t *((w:O):K)) :
    Certified O q b entry a s ↔
      ∀ t, 0<q t → InLattice O s (M t * a t) := by
  rw [independent_entries_iff]
  constructor
  · intro H t ht
    obtain ⟨r,i,j,w,h⟩ := attain t ht
    have hh := H ⟨t,r⟩ i j
    rw [h] at hh
    have hm := lattice_mul_integral O s hh ((w⁻¹:Oˣ):O)
    have he : M t*((w:O):K)*a t*(((w⁻¹:Oˣ):O):K) = M t*a t := by
      calc
        _ = M t*a t*(((w:O):K)*(((w⁻¹:Oˣ):O):K)) := by ac_rfl
        _ = _ := by rw [←Subring.coe_mul,Units.mul_inv,Subring.coe_one,mul_one]
    rwa [he] at hm
  · intro H x i j
    obtain ⟨u,hu⟩ := bound x i j
    rw [hu,mul_right_comm]
    exact lattice_mul_integral O s (H x.1 (Nat.zero_lt_of_lt x.2.isLt)) u

#print axioms lattice_rescale_iff
#print axioms exact_scaled_generator
#print axioms independent_entries_iff
#print axioms attained_envelope_iff
end Paper5.P3
