import J6R24MeteredRecursionActive
import J6R24MeteredRecursionLedger

/-! Each prepared centre itinerary exhausts the genuine dependent
address type exactly once. The equality compares the nested actual
probe/tuple/group order with the order-insensitive sum over native
slots; it does not identify, deduplicate, or memoize equal children. -/
namespace J6R24MeteredRecursion
open scoped Polynomial BigOperators
open Polynomial A1R10 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R22Active J6R16ModeCost

theorem complete_list_sum {A : Type*} [Fintype A] (xs : List A) (nu : xs.Nodup)
    (all : ∀ x,x∈xs) (f : A→ℕ) : (xs.map f).sum=∑ x,f x := by
  classical
  rw [←List.sum_toFinset f nu]
  have H : xs.toFinset=Finset.univ := by ext x; simp [all x]
  rw [H]

variable {f : ℤ[X]} {ell s : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {c : Call (PhysicalHost f ell)}
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable {bank : Bank f}

def addressed (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t)
    (g : Fin 64) : (Plan sel).Slot c := ⟨⟨t,z,β,g⟩,d.active⟩

noncomputable def liveEquiv : NativeAddress (N sel) c ≃ (Plan sel).Slot c where
  toFun w := ⟨w,d.active⟩
  invFun w := w.val
  left_inv _ := rfl
  right_inv _ := rfl

set_option maxHeartbeats 1500000 in
theorem child_sum_exact (D : ActiveDesc sel d bank) (hv : 0<ell)
    (child : ActiveChild (sel:=sel) (d:=d) bank)
    (f : (Plan sel).Slot c→ℕ)
    (actual : ∀ t z β g,(child t z β g).steps=f (addressed d t z β g)) :
    D.children hv child=@Finset.sum ((Plan sel).Slot c) ℕ _
      (@Finset.univ _ ((Plan sel).finiteSlot c)) f := by
  classical
  letI : ∀ t : Center S c, Fintype (NativeMenu (N sel) c t) :=
    fun t=>Finset.fintypeCoeSort (@J6RecursiveMenu.menu ((N sel).Mode c t) ((N sel).finiteMode c t)
      ((N sel).decideMode c t) (registerPrecision S c t) ((N sel).weight c t))
  letI : Fintype ((Plan sel).Slot c) := (Plan sel).finiteSlot c
  letI : Fintype (NativeAddress (N sel) c) := Sigma.instFintype
  have eq := Fintype.sum_equiv (liveEquiv (sel:=sel) d) (fun w=>f (liveEquiv d w)) f (fun _=>rfl)
  rw [←eq,Fintype.sum_sigma]
  change (D.centres.map (fun t=>((probeOrder _).map (fun z=>probeEntryBill (D.tape t).modes
    (child t z))).sum)).sum=_
  rw [complete_list_sum D.centres D.centreUnique D.centreComplete]
  refine Finset.sum_congr rfl (fun t _=>?_)
  rw [Fintype.sum_prod_type,probeOrder,List.map_ofFn,List.sum_ofFn]
  refine Finset.sum_congr rfl (fun z _=>?_)
  rw [Fintype.sum_prod_type]
  simp only [Function.comp_apply]
  unfold probeEntryBill
  rw [complete_list_sum _ (D.tape t).modeUnique (D.tape t).modeComplete]
  refine Finset.sum_congr rfl (fun β _=>?_)
  rw [bill,groupOrder,List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply]
  exact Finset.sum_congr rfl (fun g _=>actual t z β g)

theorem leaf_has_no_child (h : c.edges≤(S).cutoff) : childList (Plan sel) c=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro u hu
  obtain ⟨v,_,_⟩ := List.mem_map.mp hu
  exact (Nat.not_lt_of_ge h) v.property

#print axioms child_sum_exact
#print axioms leaf_has_no_child
end J6R24MeteredRecursion


