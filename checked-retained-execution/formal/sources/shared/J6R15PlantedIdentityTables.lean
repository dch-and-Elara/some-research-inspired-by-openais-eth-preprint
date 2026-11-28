import J6R12RepackBoolean
import J6R11IntegralRetained
import J6ZeroTransportSource
import J6OrientedHostEval

/-! Read the actual original root gates at a larger receiving precision:
the only allowed canonical representatives here are the real 0/1 entries
of the planted CNF and subdivision equalities. -/
namespace J6R15PlantedIdentity
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R10Integral
open J6R11Integral J6R11Repack J6R12Repack J6OrientedHost J6OrientedHostEval
open J6RecursivePortCube J6ZeroTransport
noncomputable section

variable {S V : Type*} [LinearOrder S] [Fintype S] [Fintype V] {a b m q l : ℕ}

theorem old_table_receives (f : ℤ[X]) (ell base p : ℕ) (T : Plant V m q)
    (w : Fin a → S) (hf : f.Monic) (hb : 0<base) (hd : 0<f.natDegree) (hℓ : 0<ell)
    (y : Wire w m b l→Bool) :
    reduce p f ell (rowProduct (rootNetwork T w) (rootEntryFile f ell base T w) hf y) =
      if oldOK T w y then 1 else 0 := by
  unfold rowProduct oldOK
  rw [map_prod]
  calc
    _ = ∏ v : Left V w m b l, if rowTable T w v (fun j => y (rowPort T w v j)) then (1:Box f ell p) else 0 := by
      refine Finset.prod_congr rfl (fun v _ => ?_)
      rw [actual_root_table_integral f ell base T w hf hb hd hℓ y (.inl v)]
      cases hv : rowTable T w v (fun j => y (rowPort T w v j)) <;> simp [rootFlag,hv]
    _ = _ := prod_flags _

omit [Fintype V] in
theorem new_table_receives (f : ℤ[X]) (ell base p : ℕ) (T : Plant V m q)
    (w : Fin a → S) (hf : f.Monic) (hb : 0<base) (hd : 0<f.natDegree) (hℓ : 0<ell)
    (x : Wire w m b l→Bool) :
    reduce p f ell (colProduct (rootNetwork T w) (rootEntryFile f ell base T w) hf x) =
      if newOK T w x then 1 else 0 := by
  unfold colProduct newOK
  rw [map_prod]
  calc
    _ = ∏ v : Right w m b l q, if colTable w v (fun j => x (colPort T w v j)) then (1:Box f ell p) else 0 := by
      refine Finset.prod_congr rfl (fun v _ => ?_)
      rw [actual_root_table_integral f ell base T w hf hb hd hℓ x (.inr v)]
      cases hv : colTable w v (fun j => x (colPort T w v j)) <;> simp [rootFlag,hv]
    _ = _ := prod_flags _

/-- The same independent Boolean row and column bits are read on both
sides; this expands original gate indicators, not a new tensor network. -/
theorem contract_flags {E R : Type*} [Fintype E] [DecidableEq E] [CommRing R]
    (W : E→E→R) (A B : (E→Bool)→Bool) :
    J6R10Integral.contract W (fun y => if A y then 1 else 0) (fun x => if B x then 1 else 0) =
      literalContraction W A B := by
  unfold J6R10Integral.contract literalContraction
  refine Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ]))
    (fun y _ => Finset.sum_congr (Finset.ext (fun _ => by simp only [Finset.mem_univ])) (fun x _ => ?_))
  cases ha : A y <;> cases hb : B x <;> simp [ha,hb]
  change (∏ i : E, (if y i then (∑ j, if x j then W i j else 0) else 1-(∑ j, if x j then W i j else 0)) : R) = _
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hz : (∑ j, if x j then W i j else 0) = literalRow W i x := by
    unfold literalRow
    refine Finset.sum_congr rfl fun j _ => ?_
    cases x j <;> simp
  (rw [hz]; rfl)

#print axioms old_table_receives
#print axioms new_table_receives
#print axioms contract_flags
end
end J6R15PlantedIdentity
