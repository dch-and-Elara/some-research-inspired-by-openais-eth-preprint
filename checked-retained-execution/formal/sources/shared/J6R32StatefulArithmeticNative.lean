import J6R32StatefulArithmeticChronActive
import J6R32StatefulArithmeticPath
import J6R32StatefulArithmeticRead
import J6R32StatefulArithmeticFrameWords

/-! A fixed typed resident plan, exact native slots, and live recursive
execution; no previous walk materializes or installs the jobs. The
arithmetic at a parent receives the result of its actual child call.
The reference and the chronological ledger are proof-only functions. -/
namespace J6R32StatefulArithmetic
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry

variable {f : ℤ[X]} {ell s C key prec tw bw : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => AnyLedger f ell key prec tw bw
local notation "J" => GJob f ell key prec tw bw

structure Resident (T : Prepared cfg sel r hf) (key prec tw bw : ℕ) where
  births : Births T key prec tw bw
  rootLive : AnyLedger f ell key prec tw bw→Prop
  stableRoot : StableBank rootLive
  leaf : ∀ {c : Call (PhysicalHost f ell)},Path sel r c→c.edges≤(S).cutoff→LeafCode c key
  sourceLeaf : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel r c) (stop : c.edges≤(S).cutoff) (B : AnyLedger f ell key prec tw bw),
    Ancestors births rootLive p B→∀ (x : Fin c.edges→Bool) v,
      (T.frame p.reached).decode ((leaf p stop).read hf (T.frame p.reached) T.vPositive B v (List.ofFn x)).result=
        (c.host.file v).read hf c.prec
          (assignment c.host.network (x∘c.host.edgeOrder c.edges (leaf p stop).sameEdges) v)

variable {T : Prepared cfg sel r hf}
variable (K : Resident T key prec tw bw)

set_option maxHeartbeats 4200000 in
noncomputable def native (c : Call (PhysicalHost f ell)) (p : Path sel r c) :
    SM L (Block (T.frame p.reached) ell) :=
  if stop : c.edges≤(S).cutoff then
    fun B=>let out := (K.leaf p stop).execute hf (T.frame p.reached) T.vPositive B
           ⟨(out.result,B),out.steps⟩
  else
    let active := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel p.reached T.rootStable active
    activeS (T.active c p.reached active) (reachable_positive T p.reached) T.vPositive hf
      (fun t z m g=>
        let w := addressed (sel:=sel) d t z m g
        withPublished (K.births p w).job (native ((Plan sel).child c w) (.step p w))
          (zeroM (T.bank (registerPrecision S c t) (register_positive d t)).hp))
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

set_option maxHeartbeats 4200000 in
noncomputable def reference (T : Prepared cfg sel r hf) (c : Call (PhysicalHost f ell))
    (p : NativeReach (Plan sel) r c) : Meter (Block (T.frame p) ell) :=
  if stop : c.edges≤(S).cutoff then bare (T.run c p) else
    let active := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel p T.rootStable active
    (T.active c p active).eval (reachable_positive T p) T.vPositive hf (fun t z m g=>
      let w := addressed (sel:=sel) d t z m g
      reference T ((Plan sel).child c w) (reach_snoc (Plan sel) p w))
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

set_option maxHeartbeats 4200000 in
noncomputable def nativeLog (c : Call (PhysicalHost f ell)) (p : Path sel r c) : Log L J :=
  if stop : c.edges≤(S).cutoff then
    ⟨[],fun B=>((K.leaf p stop).execute hf (T.frame p.reached) T.vPositive B).steps⟩
  else
    let active := Nat.lt_of_not_ge stop
    let d := ready_reachable cfg sel p.reached T.rootStable active
    callLog (T.active c p.reached active) (fun t z m g=>
      let w := addressed (sel:=sel) d t z m g
      Log.enter (K.births p w).job (nativeLog ((Plan sel).child c w) (.step p w)))
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

variable {c : Call (PhysicalHost f ell)} (p : Path sel r c)

theorem native_leaf (stop : c.edges≤(S).cutoff) (B : L) :
    native K c p B=⟨(((K.leaf p stop).execute hf (T.frame p.reached) T.vPositive B).result,B),
      ((K.leaf p stop).execute hf (T.frame p.reached) T.vPositive B).steps⟩ := by
  rw [native,dif_pos stop]

theorem log_leaf (stop : c.edges≤(S).cutoff) :
    nativeLog K c p=⟨[],fun B=>((K.leaf p stop).execute hf (T.frame p.reached) T.vPositive B).steps⟩ := by
  rw [nativeLog,dif_pos stop]

theorem reference_leaf (reached : NativeReach (Plan sel) r c) (stop : c.edges≤(S).cutoff) :
    reference T c reached=bare (T.run c reached) := by
  rw [reference,dif_pos stop]

#print axioms native
#print axioms nativeLog
#print axioms native_leaf
#print axioms log_leaf
#print axioms reference_leaf
end J6R32StatefulArithmetic
