import J6R49DFSRun
import J6R49DFSEmitWidth

/-! Tie the emission's next group to the whole scoped interpreter's
real recursive invocation. This code issues the precise addressed
Plan-child occurrence into the stateful bank and then restores the
parent. No selected observation must be constructed at runtime. -/
namespace J6R49DFS
open scoped Polynomial
open AOracleMachineTime A1R10 J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R48DFS J6R16ModeCost J6R49LiveBits

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2700
set_option maxHeartbeats 8500000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

noncomputable def actualChildRead (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (B : L) (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
    let d := ready_reachable cfg sel p.reached T.rootStable a
    Meter (Block (T.bank (registerPrecision S c t) (register_positive d t)) ell) :=
  let d := ready_reachable cfg sel p.reached T.rootStable a
  let w := addressed (sel:=sel) d t z β g
  project (withScope retire (R.births p w).job
    (nativeStream R retire ((Plan sel).child c w) (.step p w))
    (zeroM (T.bank (registerPrecision S c t) (register_positive d t)).hp) B)

theorem active_phase_is_same_runner (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ)
    (p : Path sel r c) (a : (S).cutoff<c.edges) (B : L) :
    nativeStream R retire c p B=
      let out := (R.active p a).eval R.modeWidth (reachable_positive T p.reached) T.vPositive hf
        (actualChildRead R retire p a B)
      (⟨(out.result,B),out.steps⟩ : Meter (Block (T.frame p.reached) ell×L)) := by
  rw [nativeStream,dif_neg (Nat.not_le.mpr a)]
  rfl

theorem true_child_transaction (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (initial : L) (valid : ReadyOnStack R.births initial)
    (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
    let B := stackBank R.births initial p
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let w := addressed (sel:=sel) d t z β g
    let j := (R.births p w).job
    let new := stackBank R.births initial (.step p w)
    let out := nativeStream R retire ((Plan sel).child c w) (.step p w) new
    actualChildRead R retire p a B t z β g=
      (⟨out.result.1,publishFee B j.entry j.offset j.built+out.steps+retire j+4⟩ :
        Meter (Block (T.bank (registerPrecision S c t) (register_positive d t)) ell)) ∧
    out.result.2=new := by
  let B := stackBank R.births initial p
  let d := ready_reachable cfg sel p.reached T.rootStable a
  let w := addressed (sel:=sel) d t z β g
  let j := (R.births p w).job
  let bad : Meter (Block (T.bank (registerPrecision S c t) (register_positive d t)) ell) :=
    zeroM (T.bank (registerPrecision S c t) (register_positive d t)).hp
  refine ⟨?_,stream_restores_bank R retire ((Plan sel).child c w) (.step p w) _⟩
  change project (withScope retire j (nativeStream R retire ((Plan sel).child c w) (.step p w)) bad B)=_
  rw [paid_scope_exact retire j _ bad B (valid p w)]
  rfl

#print axioms active_phase_is_same_runner
#print axioms true_child_transaction
end J6R49DFS
