import J6R49DFSVisitMath
import J6R49LivePeak

/-! The bounded fields are the exact pre-child buffers of a particular
reachable emitted exponent vector and group. The same outer and inner
values occur in the exact measured continuation. -/
namespace J6R49DFS
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply J6R32StatefulArithmetic J6R48DFS
open J6R49LiveBits

set_option autoImplicit false
set_option maxHeartbeats 10500000
set_option maxRecDepth 2400

variable {f : ℤ[X]} {ell s C q : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

theorem literal_emission_fields_and_continuation (cfg : RootBounds s C f) (hr : Stable s C r)
    (zero : r.depth=0) (bound : r.prec≤C*s) (p : Path sel r c)
    (d : Ready S (sourceDelta s) c) (t : Center S c)
    (F : Frame f (registerPrecision S c t)) (hf : f.Monic)
    (I : SiteTape sel d t q) (hq : 0<q) (qFit : q≤uniformWidth s C) (hv : 0<ell)
    (child : NativeMenu (N sel) c t→Fin 64→Meter (Block F ell))
    (startState : Pending q I.words.length) (start : (startingCursor I hq).result=some startState)
    (Q : Pending q I.words.length) (outer : Block F ell) (fee : ℕ)
    (previous : ModePrefix (modeUpdate F I hv child) startState
      (zeroM (ell:=ell) (f:=F.words) F.hp).result
      ((zeroM (ell:=ell) (f:=F.words) F.hp).steps+(startingCursor I hq).steps) Q outer fee)
    (v : List (J6R15ModeCost.Word q)) (z : J6R15ModeCost.State q) (emit : Q.pulse.result=.emit v z)
    (β : NativeMenu (N sel) c t) (hβ : decodeAt I v=some β) (g : Fin 64)
    (left : List (Fin 64)) (inner : Block F ell) (feeM : ℕ)
    (grown : GroupPrefix F.hp (child β) (oneM F.hp F.sizePos hv).result
      (oneM F.hp F.sizePos hv).steps (g::left) inner feeM) :
    let observation : NativeSuspension (C:=C) (sel:=sel) c :=
      ⟨d,t,q,qFit,I,Q.state,Q.valid,F,outer,inner⟩
    let mul := mulM F.hp ⟨inner,0⟩ (child β g)
    let prod := productCursor F.hp (child β) left mul.result (feeM+mul.steps)
    let sum := addM F.hp ⟨outer,0⟩ prod
    let tail := modeDrain (modeUpdate F I hv child) (Q.tail emit) sum.result (fee+Q.pulse.steps+sum.steps)
    observation.measure.bits ≤ frameBase (uniformWidth s C) (rosterSize s C)+
      c.edges*frameSlope s C ell f.natDegree ∧
    runProbe F I hq hv child=⟨tail.result.1,tail.steps⟩ := by
  dsimp only
  refine ⟨?_,probe_halts_after_actual_child F I hq hv child startState start Q outer fee previous v z emit
    β hβ g left inner feeM grown⟩
  exact real_tape_suspension_fit cfg hr zero bound p.reached d t qFit I hf F Q.state Q.valid outer inner

#print axioms literal_emission_fields_and_continuation
end J6R49DFS
