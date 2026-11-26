import PrecisionErasure
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-! Exact early parity divisibility for quadratic Boolean tests, using
the idempotent support sum. A mask represents a complete assignment
of original Boolean variables, not just a protected fiber. -/
namespace Paper5.FrontendG1
open scoped BigOperators

abbrev F₂ := ZMod 2

def phase (a : F₂) : ℤ := if a=0 then 1 else -1

theorem binary_cases : ∀ a : F₂,a=0 ∨ a=1 := by decide

theorem phase_add : ∀ a b : F₂,phase (a+b)=phase a*phase b := by decide

theorem phase_sum {I : Type*} (s : Finset I) (f : I→F₂) :
    phase (∑ i ∈ s,f i)=∏ i ∈ s,phase (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [phase]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi,phase_add,ih]

structure Quad (V : Type*) where
  terms : List (Finset V)
  small : ∀ t∈terms,t.card≤2

variable {V : Type*} [DecidableEq V]

def mon {R : Type*} [Zero R] [One R] (u x : Finset V) : R :=
  if u⊆x then 1 else 0

def Quad.eval (q : Quad V) (x : Finset V) : F₂ :=
  (q.terms.map (fun u=>mon u x)).sum

theorem eval_indexed (q : Quad V) (x : Finset V) :
    q.eval x=∑ j : Fin q.terms.length,mon (q.terms.get j) x := by
  rw [←List.sum_ofFn]
  change (q.terms.map (fun u=>mon (R:=F₂) u x)).sum =
    (List.ofFn ((fun u=>mon (R:=F₂) u x) ∘ q.terms.get)).sum
  rw [←List.map_ofFn,List.ofFn_get]

def unionPicked (q : Quad V) (s : Finset (Fin q.terms.length)) : Finset V :=
  s.biUnion q.terms.get

theorem union_picked_size (q : Quad V) (s : Finset (Fin q.terms.length)) :
    (unionPicked q s).card≤2*s.card := by
  calc
    _ ≤ ∑ i ∈ s,(q.terms.get i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ s,2 := Finset.sum_le_sum (fun i _=>q.small _ (List.get_mem _ _))
    _ = _ := by simp [Nat.mul_comm]

theorem phase_eval_product (q : Quad V) (x : Finset V) :
    phase (q.eval x)=∏ j : Fin q.terms.length,(1+(if q.terms.get j⊆x then (-2:ℤ) else 0)) := by
  rw [eval_indexed,phase_sum]
  apply Finset.prod_congr rfl
  intro i _
  unfold mon
  split_ifs <;> norm_num [phase]

private theorem phase_prod_union (q : Quad V) (s : Finset (Fin q.terms.length)) (x : Finset V) :
    (∏ j ∈ s,if q.terms.get j⊆x then (-2:ℤ) else 0) =
      if unionPicked q s⊆x then (-2:ℤ)^s.card else 0 := by
  by_cases H : unionPicked q s⊆x
  · rw [if_pos H,←Finset.prod_const]
    apply Finset.prod_congr rfl
    intro j hj
    exact if_pos (fun b hb=>H (Finset.mem_biUnion.mpr ⟨j,hj,hb⟩))
  · rw [if_neg H]
    obtain ⟨v,hv,hx⟩ := Finset.not_subset.mp H
    obtain ⟨j,hj,hv'⟩ := Finset.mem_biUnion.mp hv
    apply Finset.prod_eq_zero hj
    exact if_neg (fun h=>hx (h hv'))

noncomputable def walsh [Fintype V] (q : Quad V) : ℤ :=
  ∑ x : Finset V,phase (q.eval x)

theorem walsh_exact_expansion [Fintype V] (q : Quad V) :
    walsh q=∑ s : Finset (Fin q.terms.length),
      (2:ℤ)^(Fintype.card V-(unionPicked q s).card)*(-2:ℤ)^s.card := by
  classical
  unfold walsh
  simp_rw [phase_eval_product,Finset.prod_one_add]
  simp only [Finset.powerset_univ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [phase_prod_union]
  exact PrecisionErasure.sum_monomial _ _

theorem quadratic_walsh_divisible [Fintype V] (q : Quad V) (N : ℕ)
    (hV : Fintype.card V=2*N) : (2:ℤ)^N ∣ walsh q := by
  rw [walsh_exact_expansion]
  apply Finset.dvd_sum
  intro s _
  have hS := union_picked_size q s
  have hU : (unionPicked q s).card≤Fintype.card V := by
    exact Finset.card_le_univ _
  have h : N≤Fintype.card V-(unionPicked q s).card+s.card := by omega
  have he : (2:ℤ)^(Fintype.card V-(unionPicked q s).card)*(-2:ℤ)^s.card =
      (2:ℤ)^(Fintype.card V-(unionPicked q s).card+s.card)*(-1:ℤ)^s.card := by
    rw [show (-2:ℤ)=2*(-1) by decide,mul_pow,pow_add,mul_assoc]
  rw [he]
  exact dvd_mul_of_dvd_left (pow_dvd_pow _ h) _

def zeroQuad (V : Type*) : Quad V := ⟨[],by simp⟩

def addQuad (q r : Quad V) : Quad V :=
  ⟨q.terms++r.terms,by
    intro u h
    rcases List.mem_append.mp h with h|h
    · exact q.small u h
    · exact r.small u h⟩

def scaleQuad (a : F₂) (q : Quad V) : Quad V :=
  if a=0 then zeroQuad V else q

theorem eval_zero_quad (x : Finset V) : (zeroQuad V).eval x=0 := rfl

theorem eval_add_quad (q r : Quad V) (x : Finset V) :
    (addQuad q r).eval x=q.eval x+r.eval x := by
  simp [addQuad,Quad.eval]

theorem eval_scale_quad (a : F₂) (q : Quad V) (x : Finset V) :
    (scaleQuad a q).eval x=a*q.eval x := by
  rcases binary_cases a with rfl|rfl
  · simp [scaleQuad,eval_zero_quad]
  · simp [scaleQuad]

def listCombine {I : Type*} (q : I→Quad V) (a : I→F₂) : List I→Quad V
  | [] => zeroQuad V
  | i::is => addQuad (scaleQuad (a i) (q i)) (listCombine q a is)

theorem eval_list_combine {I : Type*} (q : I→Quad V) (a : I→F₂) (l : List I) (x : Finset V) :
    (listCombine q a l).eval x=(l.map (fun i=>a i*(q i).eval x)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [listCombine,eval_add_quad,eval_scale_quad,ih]

noncomputable def combine {I : Type*} [Fintype I] (q : I→Quad V) (a : I→F₂) : Quad V :=
  listCombine q a (Finset.univ : Finset I).toList

theorem eval_combine {I : Type*} [Fintype I] (q : I→Quad V) (a : I→F₂) (x : Finset V) :
    (combine q a).eval x=∑ i,a i*(q i).eval x := by
  rw [combine,eval_list_combine,Finset.sum_map_toList]

#print axioms phase_add
#print axioms phase_sum
#print axioms eval_indexed
#print axioms union_picked_size
#print axioms phase_eval_product
#print axioms walsh_exact_expansion
#print axioms quadratic_walsh_divisible
#print axioms eval_combine
end Paper5.FrontendG1