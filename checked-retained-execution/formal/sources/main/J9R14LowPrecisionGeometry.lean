import J9R14LowPrecisionHalf
import J9R14LowPrecisionLinear
import J6R10RowLocal
import OuterNodePacking

/-!
# Real row ports enforce the zero-constant restriction

Padding is excluded by constructing the real predicates as images of
actual row and column ports. A constant on an untouched owner would
exhibit an actual matched column, contradicting the definition.
-/

namespace J9R14LowPrecisionGeometry
open scoped Polynomial Classical BigOperators
open Polynomial OuterNodePacking DenominatorBudget J9R14LowPrecisionHalf
open J9R14LowPrecisionLinear

noncomputable section

variable {P V Row Col : Type*} {L : ℕ}
variable [Fintype Row] [Fintype Col]

structure Seats (P Row Col : Type*) (L : ℕ) where
  row : Row→Slot P L
  col : Col→Slot P L

def rowReal (d : Seats P Row Col L) (s : Slot P L) : Bool := decide (∃ r, d.row r=s)

def colReal (d : Seats P Row Col L) (s : Slot P L) : Bool := decide (∃ c, d.col c=s)

def coeffEntry (d : Seats P Row Col L) (a : ℕ) (t : ℤ)
    (take : Row→Col→Prop) (r : Row) (c : Col) : TwoLocal[X] :=
  if (d.col c).1=(d.row r).1 ∧ take r c
  then wHalf a t (((d.col c).2.val:ℤ)-((d.row r).2.val:ℤ))
  else 0

omit [Fintype Row] [Fintype Col] in
theorem coeff_entry_constant (d : Seats P Row Col L) (a : ℕ) (t : ℤ)
    (take : Row→Col→Prop) (r : Row) (c : Col) :
    (coeffEntry d a t take r c).coeff 0 =
      if ((d.col c).1=(d.row r).1 ∧ take r c) ∧
        ((d.col c).2.val:ℤ)-((d.row r).2.val:ℤ)=t then J6R9PacketCoeff.rho a t else 0 := by
  by_cases h : (d.col c).1=(d.row r).1 ∧ take r c <;>
    simp [coeffEntry,h,w_constant]

variable [Fintype P]

def kept (d : Seats P Row Col L) (old : Finset V) (owner : Slot P L→V) (t : ℤ) : Finset V :=
  untouched old owner (matchedColumns Finset.univ (rowReal d) (colReal d) t)

theorem untouched_constant_zero (d : Seats P Row Col L) (a : ℕ) (t : ℤ)
    (old : Finset V) (owner : Slot P L→V) (take : Row→Col→Prop)
    (r : Row) (c : Col) (hFree : owner (d.col c)∈kept d old owner t) :
    (coeffEntry d a t take r c).coeff 0=0 := by
  rw [coeff_entry_constant]
  apply if_neg
  intro h
  have hy : d.col c ∈ matchedColumns Finset.univ (rowReal d) (colReal d) t :=
    (mem_matchedColumns _ _ _ _ _).mpr
      ⟨Finset.mem_univ _,by simp [colReal],(d.row r).2,by
        unfold rowReal
        exact decide_eq_true ⟨r,Prod.ext h.1.1.symm rfl⟩,by omega⟩
  exact untouched_no_matched_port old owner _ hFree (d.col c) hy rfl

section ActualRows
open P11FullPacking J6R9PacketScopes J6R10RowLocal J6R9PacketChild
variable {S Q T : Type*} [LinearOrder S] [Fintype Q] {a b : ℕ}

def nativeSeats (ρ : T→Physical a b S) (κ : Q→Physical a b S) :
    Seats (Page a b S) T Q (2^a) := ⟨ρ,κ⟩

def rowPoly (ρ : T→Physical a b S) (κ : Q→Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) (t : ℤ) (r : T) (X : Q→Bool) : TwoLocal[X] :=
  ∑ q : Q, coeffEntry (nativeSeats ρ κ) a t
    (fun r q => colGroup mask i (κ q)=rowGroup mask i (ρ r)) r q *
      C (J6R9PacketTiles.bit TwoLocal (X q))

theorem rowPoly_is_native {K : Type*} [CommRing K]
    (ρ : T→Physical a b S) (κ : Q→Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) (t : ℤ) (r : T)
    (p : ℕ) (hnil : (2:K)^p=0) (z : K) (X : Q→Bool) :
    (rowPoly ρ κ mask i t r X).eval₂ (J6ZeroTransport.reduceAt p hnil) (2*z) =
      localValue κ mask i t p hnil z (ρ r) (fun q => X q.val) := by
  rw [local_as_filter,rowPoly,Polynomial.eval₂_finset_sum]
  apply Finset.sum_congr rfl
  intro q _
  by_cases h : colGroup mask i (κ q)=rowGroup mask i (ρ r)
  · by_cases hh : (κ q).1=(ρ r).1
    · simp only [coeffEntry,nativeSeats,hh,h,and_self,if_true,columnEntry,Polynomial.eval₂_mul,
        w_eval_half,Polynomial.eval₂_C]
      cases X q <;> simp [J6R9PacketTiles.bit]
    · simp [coeffEntry,nativeSeats,h,hh,columnEntry]
  · simp [coeffEntry,nativeSeats,h]

end ActualRows

#print axioms coeff_entry_constant
#print axioms untouched_constant_zero
#print axioms rowPoly_is_native

end
end J9R14LowPrecisionGeometry
