import J6R49LiveCanonical
import J6R49DFSRun

/-! All active occurrences use the same sufficient common Hermite
scale. Only the representation of the accumulator changes; the
selected physical children, tape, directory and leaf adapter are kept. -/
namespace J6R49LiveBits
open scoped Polynomial
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R9Recursive
open J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS

set_option autoImplicit false
set_option maxHeartbeats 4500000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

def canonicalStreaming (R : StreamingResident T key prec tw bw page q) :
    StreamingResident T key prec tw bw page q :=
  { R with active := fun p h => canonicalActive (R.active p h) }

theorem every_canonical_common_field_has_bound
    (R : StreamingResident T key prec tw bw page q) (hzero : r.depth=0) (hroot : r.prec≤C*s)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (active : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges) :
    let lam := Nat.clog 2 s
    c.prec+((canonicalStreaming R).active p active).extraPrecision≤
      J6R16ModeCost.precisionSize s C+c.edges*(24*2^lam+4*(lam+1)) :=
  canonical_common_field_budget cfg T.rootStable p.reached hzero hroot (R.active p active)

theorem canonical_whole_stream [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (R : StreamingResident T key prec tw bw page q)
    (retire : J6R33StatefulArithmeticPage.PageJob f ell key prec tw bw page→ℕ)
    (initial : PageBank f ell key prec tw bw page)
    (origin : R.rootLive initial) (valid : ReadyOnStack R.births initial) :
    let run := nativeStream (canonicalStreaming R) retire r .root initial
    (T.frame (NativeReach.reflexive r)).decode run.result.1=(sourceBlueprint sel r hf).program.run r ∧
      run.result.2=initial :=
  whole_stream_scoped_source (canonicalStreaming R) retire initial origin valid

#print axioms every_canonical_common_field_has_bound
#print axioms canonical_whole_stream
end J6R49LiveBits

