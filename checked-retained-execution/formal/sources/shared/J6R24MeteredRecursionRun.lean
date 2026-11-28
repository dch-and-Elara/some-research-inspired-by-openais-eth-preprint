import J6R24MeteredRecursionNativeLedger
import J6R16ModeCostPath

/-! One well-founded *native* call interpreter, before the proof-side
ledger is read. It does not enumerate a global padded Mode alphabet.
A given descriptor supplies binary probe masks, legal ordered tuples,
prepared UV moduli, and the existing executable leaf entry readers.
Physical child/descriptor preparation and top-level decoding remain
separate. The dependent indexing is proof-level, not a claim of a
byte-coded descriptor loader. -/
namespace J6R24MeteredRecursion
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R21Ancestor

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell)) (hf : f.Monic)
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

structure Prepared where
  rootStable : Stable s C r
  rootPositive : 0<r.prec
  vPositive : 0<ell
  bank : Bank f
  leaf : NativeLeafTapes sel r hf
  active : ∀ c (hc : NativeReach (Plan sel) r c) (ha : (S).cutoff<c.edges),
    ActiveDesc sel (ready_reachable cfg sel hc rootStable ha) bank

variable {cfg sel r hf}
variable (T : Prepared cfg sel r hf)

include T in
theorem reachable_positive {c : Call (PhysicalHost f ell)}
    (h : NativeReach (Plan sel) r c) : 0<c.prec := by
  refine nativeReach_run_invariant (Plan sel) (fun x=>0<x.prec) ?_ h T.rootPositive
  intro x _ w
  change 0<registerPrecision S x w.val.1
  exact (Nat.zero_le x.prec).trans_lt
    (child_monotone x.prec _ _ _ w.val.1.val (Nat.zero_lt_of_lt w.property))

abbrev Prepared.frame {c : Call (PhysicalHost f ell)} (hc : NativeReach (Plan sel) r c) :=
  T.bank c.prec (reachable_positive T hc)

set_option maxHeartbeats 3800000 in
noncomputable def Prepared.run (c : Call (PhysicalHost f ell)) (hc : NativeReach (Plan sel) r c) :
    Meter (Block (T.frame hc) ell) :=
  if h : c.edges≤(S).cutoff then convertLeaf (T.leaf c hc h) (T.frame hc) else
    let ha := Nat.lt_of_not_ge h
    let d := ready_reachable cfg sel hc T.rootStable ha
    (T.active c hc ha).eval (reachable_positive T hc) T.vPositive hf (fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      run ((Plan sel).child c w) (reach_snoc (Plan sel) hc w))
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

set_option maxHeartbeats 1800000 in
noncomputable def Prepared.childRuns {c : Call (PhysicalHost f ell)}
    (hc : NativeReach (Plan sel) r c)
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c) :
    ActiveChild (sel:=sel) (d:=d) T.bank :=
  fun t z β g=>
    let w := addressed (sel:=sel) d t z β g
    T.run ((Plan sel).child c w) (reach_snoc (Plan sel) hc w)

theorem Prepared.run_leaf {c : Call (PhysicalHost f ell)}
    (hc : NativeReach (Plan sel) r c) (h : c.edges≤(S).cutoff) :
    T.run c hc=convertLeaf (T.leaf c hc h) (T.frame hc) := by
  rw [Prepared.run,dif_pos h]

set_option maxHeartbeats 2600000 in
theorem Prepared.run_active {c : Call (PhysicalHost f ell)}
    (hc : NativeReach (Plan sel) r c) (ha : (S).cutoff<c.edges) :
    T.run c hc=(T.active c hc ha).eval (reachable_positive T hc) T.vPositive hf
      (T.childRuns hc (ready_reachable cfg sel hc T.rootStable ha)) := by
  rw [Prepared.run,dif_neg (Nat.not_le.mpr ha)]
  rfl

#print axioms reachable_positive
#print axioms Prepared.run_leaf
#print axioms Prepared.run_active
end J6R24MeteredRecursion

