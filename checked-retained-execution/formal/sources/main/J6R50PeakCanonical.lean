
import J6R50PeakStack
import J6R49LiveCanonicalRun

/-! A single canonical-precision native invocation, with its source
value, directory restoration, and a pointwise peak bound on the
selected physical payloads at every actual ancestral suspension.
Validity of the prepared atlas and raw source descriptors is unchanged. -/
namespace J6R50Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS J6R49LiveBits

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 21000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

theorem actual_canonical_high_fits (R : StreamingResident T key prec tw bw page q)
    (d₀ : r.depth=0) (p₀ : r.prec≤C*s) : HighFit (canonicalStreaming R) :=
  fun p ac => every_canonical_common_field_has_bound R d₀ p₀ p ac

theorem canonical_exact_payload_any_source_path
    (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (d₀ : r.depth=0) (p₀ : r.prec≤C*s) (qFit : q≤uniformWidth s C)
    (pageBound : ℕ) (rows : AllExactPages R.births)
    (bits : ∀ {x : Call (PhysicalHost f ell)} (path : Path sel r x) (w : (Plan sel).Slot x),
      let e := (R.births path w).job.immutable.payload.payload
      ∀ y∈e.pages,(originPayload y.payload).length≤pageBound)
    (p : Path sel r c) :
    ∃ m n,JointSuspensions (canonicalStreaming R) retire initial p m n ∧
      residentAtlasBits (stackBank R.births initial p)+m+n≤
        selectedRoof (s:=s) (C:=C) initial r.edges pageBound := by
  obtain ⟨m,n,trace⟩ := every_source_path_has_joint_suspensions
    (canonicalStreaming R) retire initial qFit p
  exact ⟨m,n,trace,joint_scoped_selected_peak (canonicalStreaming R) retire initial p m n
    trace d₀ p₀ (actual_canonical_high_fits R d₀ p₀) pageBound rows bits⟩

theorem canonical_source_value_and_selected_peak
    [DecidableEq (Envelope (N sel) (Childs sel) r)]
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (origin : R.rootLive initial) (legal : ReadyOnStack R.births initial)
    (d₀ : r.depth=0) (p₀ : r.prec≤C*s) (qFit : q≤uniformWidth s C)
    (pageBound : ℕ) (rows : AllExactPages R.births)
    (bits : ∀ {x : Call (PhysicalHost f ell)} (path : Path sel r x) (w : (Plan sel).Slot x),
      let e := (R.births path w).job.immutable.payload.payload
      ∀ y∈e.pages,(originPayload y.payload).length≤pageBound) :
    let run := nativeStream (canonicalStreaming R) retire r .root initial
    (T.frame (NativeReach.reflexive r)).decode run.result.1=(sourceBlueprint sel r hf).program.run r ∧
    run.result.2=initial ∧
    ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x),
      ∃ m n,JointSuspensions (canonicalStreaming R) retire initial p m n ∧
        residentAtlasBits (stackBank R.births initial p)+m+n≤
          selectedRoof (s:=s) (C:=C) initial r.edges pageBound := by
  obtain ⟨val,restored⟩ := canonical_whole_stream R retire initial origin legal
  exact ⟨val,restored,fun p =>
    canonical_exact_payload_any_source_path R retire initial d₀ p₀ qFit pageBound rows bits p⟩

#print axioms actual_canonical_high_fits
#print axioms canonical_exact_payload_any_source_path
#print axioms canonical_source_value_and_selected_peak
end J6R50Peak
