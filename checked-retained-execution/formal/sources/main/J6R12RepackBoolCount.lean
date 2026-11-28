import J6R12RepackBoolean
import J6R11RepackRootHost

/-! Root contraction is the natural count of accepted assignments of
the literal repaired physical Boolean gate network. No interpretation
of arbitrary integer entries as Boolean values is used. -/
namespace J6R12Repack
open scoped Polynomial BigOperators
open Polynomial J6ActiveRun J6R9Recursive J6R11Repack J6R11Blueprint
open J6R10Repack J6OrientedHost P11FullPacking J6Mesh

variable {S V : Type} [LinearOrder S] [Fintype S] [Fintype V]

noncomputable def literalGateCount (m l q : ℕ) (T : Plant V m q) (w : Fin (a m) → S) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Wire w m (K m) l → Bool =>
    ∀ v : Left V w m (K m) l ⊕ Right w m (K m) l q, rootFlag T w x v = true).card

private theorem prod_bool_indicator {A R : Type*} [Fintype A] [CommRing R] (b : A → Bool) :
    (∏ v : A, if b v then (1:R) else 0) = (if ∀ v, b v = true then 1 else 0) := by
  classical
  by_cases h : ∀ v, b v = true
  · simp [h]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨v,hv⟩ := h
    have hb : b v = false := Bool.eq_false_of_not_eq_true hv
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hb])

set_option maxHeartbeats 2200000 in
theorem exact_root_integral_gate_count (f : ℤ[X]) (ell p m l q : ℕ)
    (T : Plant V m q) (w : Fin (a m) → S) (hf : f.Monic)
    (hp : 0<p) (hd : 0<f.natDegree) (hℓ : 0<ell) :
    (physicalRootCall f ell p m l q T w).host.contract hf =
      (literalGateCount m l q T w : IntRing f ell) := by
  classical
  change trueContraction (rootNetwork (b:=K m) (l:=l) T w) (rootEntryFile f ell p T w) hf = _
  unfold trueContraction literalGateCount
  calc
    _ = ∑ x : Wire w m (K m) l → Bool,
          ∏ v : Left V w m (K m) l ⊕ Right w m (K m) l q, (if rootFlag T w x v then 1 else 0) := by
         exact Finset.sum_congr rfl (fun x _ => Finset.prod_congr rfl
           (fun v _ => actual_root_table_integral f ell p T w hf hp hd hℓ x v))
    _ = ∑ x : Wire w m (K m) l → Bool,
          if ∀ v : Left V w m (K m) l ⊕ Right w m (K m) l q, rootFlag T w x v = true
             then (1 : IntRing f ell) else 0 := by
         exact Finset.sum_congr rfl (fun x _ => prod_bool_indicator (rootFlag T w x))
    _ = _ := by rw [← Finset.sum_filter]; simp

theorem literal_gate_count_bound (m l q : ℕ) (T : Plant V m q) (w : Fin (a m) → S)
    (hm : m≤K m) (hL : 2*l=L m) (hS : Fintype.card S=64) :
    literalGateCount m l q T w ≤ 2^M m := by
  classical
  unfold literalGateCount
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,
      J6RepairedCapacity.actual_wire_count m l w hm hL hS]

#print axioms literalGateCount
#print axioms exact_root_integral_gate_count
#print axioms literal_gate_count_bound
end J6R12Repack
