import J6R49DFSProbe
import J6R48DFSRun

/-! One streamed native probe whose child replies really run the
prepared R48 scoped subtrees. This local composition does not assert
those entire subtrees themselves use streaming at every depth. -/
namespace J6R49DFS
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R48DFS

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 11200000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

noncomputable def scopedProbeChild (R : PagedResident T key prec tw bw page) (retire : J→ℕ)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (B : L) (t : Center S c) (z : Probe S c) (β : NativeMenu (J6R12Blueprint.N sel) c t) (g : Fin 64) :
    let d := ready_reachable cfg sel p.reached T.rootStable a
    Meter (Block (T.bank (registerPrecision S c t) (register_positive d t)) ell) :=
  let d := ready_reachable cfg sel p.reached T.rootStable a
  let w := addressed (sel:=sel) d t z β g
  project (withScope retire (R.births p w).job (nativeScoped R retire ((Plan sel).child c w) (.step p w))
    (zeroM (T.bank (registerPrecision S c t) (register_positive d t)).hp) B)

variable [DecidableEq (J6R10Reachable.Envelope (J6R12Blueprint.N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem scoped_probe_child_exact (R : PagedResident T key prec tw bw page) (retire : J→ℕ)
    (initial : L) (origin : R.rootLive initial) (legal : ReadyOnStack R.births initial)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (t : Center S c) (z : Probe S c) (β : NativeMenu (J6R12Blueprint.N sel) c t) (g : Fin 64) :
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let F := T.bank (registerPrecision S c t) (register_positive d t)
    F.decode (scopedProbeChild R retire p a (stackBank R.births initial p) t z β g).result=
      (sourceBlueprint sel r hf).program.run ((Plan sel).child c (addressed (sel:=sel) d t z β g)) := by
  let d := ready_reachable cfg sel p.reached T.rootStable a
  let F := T.bank (registerPrecision S c t) (register_positive d t)
  let w := addressed (sel:=sel) d t z β g
  let j := (R.births p w).job
  let bad : Meter (Block F ell) := zeroM F.hp
  let B := stackBank R.births initial p
  let child := nativeScoped R retire ((Plan sel).child c w) (.step p w)
  change F.decode (project (withScope retire j child bad B)).result=_
  rw [paid_scope_exact retire j child bad B (legal p w)]
  exact (whole_scoped_source R retire initial origin legal ((Plan sel).child c w) (.step p w)).1

theorem same_scoped_probe_value (R : PagedResident T key prec tw bw page) (retire : J→ℕ)
    (initial : L) (origin : R.rootLive initial) (legal : ReadyOnStack R.births initial)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (t : Center S c) (z : Probe S c) (hq : 0<q)
    (I : SiteTape sel (ready_reachable cfg sel p.reached T.rootStable a) t q) :
    let d := ready_reachable cfg sel p.reached T.rootStable a
    let F := T.bank (registerPrecision S c t) (register_positive d t)
    let child := scopedProbeChild R retire p a (stackBank R.births initial p) t z
    let B := sourceBlueprint sel r hf
    let fromChild : Responses (paddedShape (J6R12Blueprint.N sel) (Childs sel) r) f ell c :=
      fun w=>B.program.run (B.program.child c w)
    F.decode (runProbe F I hq T.vPositive child).result=
      groupedSample (paddedShape (J6R12Blueprint.N sel) (Childs sel) r) f ell c fromChild t z := by
  let d := ready_reachable cfg sel p.reached T.rootStable a
  let F := T.bank (registerPrecision S c t) (register_positive d t)
  let child := scopedProbeChild R retire p a (stackBank R.births initial p) t z
  letI : Fintype (NativeMenu (J6R12Blueprint.N sel) c t) := nativeMenuFinite (J6R12Blueprint.N sel) c t
  let modes := (Finset.univ : Finset (NativeMenu (J6R12Blueprint.N sel) c t)).toList
  have nd : modes.Nodup := Finset.nodup_toList _
  have complete : ∀ b,b∈modes := by intro b; simp [modes]
  have word := streamed_probe_replaces_list hf F I hq T.vPositive child modes nd complete
  dsimp only
  rw [word]
  rw [Frame.decode,boxTransport_cast]
  exact (metered_native_probe sel r hf c p.reached a t z F.hp F.sizePos T.vPositive F.exactMod
    modes nd complete child (fun β g=>by
      rw [←boxTransport_cast]
      exact scoped_probe_child_exact R retire initial origin legal p a t z β g)).1

#print axioms scopedProbeChild
#print axioms scoped_probe_child_exact
#print axioms same_scoped_probe_value
end J6R49DFS
