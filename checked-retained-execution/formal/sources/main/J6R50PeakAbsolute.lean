
import J6R50PeakAbsoluteCaps
import J6R50PeakStack

/-! All pre-child payload observations of the same canonical runner at
arbitrary absolute start depth. The roof depends on the actual incoming
precision, not an unproved substitution of the depth-zero constant. -/
namespace J6R50Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS J6R49LiveBits

set_option autoImplicit false
set_option maxRecDepth 3700
set_option maxHeartbeats 20000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def absoluteSelectedRoof (initial : L) (rootEdges rootPrec pageBound : ℕ) : ℕ :=
  let P := absolutePrecision s rootEdges rootPrec
  residentAtlasBits initial+(96*rootEdges/29)*(page+pageBound)+
    pathLimit s C*(absoluteModeCap s C ell f.natDegree P+absoluteNumericCap s C ell f.natDegree P)

theorem absolute_ancestral_numeric_and_mode_bits
    {R : StreamingResident T key prec tw bw page q} {retire : J→ℕ} {initial : L}
    {p : Path sel r c} {m n : ℕ} (trace : JointSuspensions (canonicalStreaming R) retire initial p m n) :
    let P := absolutePrecision s r.edges r.prec
    m+n≤pathLimit s C*(absoluteModeCap s C ell f.natDegree P+absoluteNumericCap s C ell f.natDegree P) := by
  let P := absolutePrecision s r.edges r.prec
  let B := absoluteModeCap s C ell f.natDegree P+absoluteNumericCap s C ell f.natDegree P
  have count : m+n≤moves p*B := by
    induction trace with
    | root => simp [moves]
    | @push x p m n earlier w o seen E ih =>
      have a := mode_selected_payload_absolute T p o
      have b := numeric_selected_payload_absolute E retire initial
      have v : o.measure.bits+(E.payload retire initial).length≤B := Nat.add_le_add a b
      simp only [moves,Nat.add_mul,Nat.one_mul]
      omega
  exact count.trans (Nat.mul_le_mul_right _ (actual_ancestry_moves_any_start cfg sel T.rootStable p))

theorem actual_absolute_path_selected_peak
    (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (qFit : q≤uniformWidth s C) (pageBound : ℕ) (rows : AllExactPages R.births)
    (bits : ∀ {x : Call (PhysicalHost f ell)} (path : Path sel r x) (w : (Plan sel).Slot x),
      let e := (R.births path w).job.immutable.payload.payload
      ∀ y∈e.pages,(originPayload y.payload).length≤pageBound)
    (p : Path sel r c) :
    ∃ m n,JointSuspensions (canonicalStreaming R) retire initial p m n ∧
      residentAtlasBits (stackBank R.births initial p)+m+n≤
        absoluteSelectedRoof (s:=s) (C:=C) initial r.edges r.prec pageBound := by
  obtain ⟨m,n,trace⟩ := every_source_path_has_joint_suspensions
    (canonicalStreaming R) retire initial qFit p
  have pages := scoped_generated_literal_page_bits R.births initial pageBound rows bits p
  have memory := absolute_ancestral_numeric_and_mode_bits trace
  exact ⟨m,n,trace,(Nat.add_assoc _ _ _).le.trans (Nat.add_le_add pages memory)⟩

theorem actual_absolute_source_value_and_selected_peak
    [DecidableEq (Envelope (N sel) (Childs sel) r)]
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (origin : R.rootLive initial) (legal : ReadyOnStack R.births initial)
    (qFit : q≤uniformWidth s C) (pageBound : ℕ) (rows : AllExactPages R.births)
    (bits : ∀ {x : Call (PhysicalHost f ell)} (path : Path sel r x) (w : (Plan sel).Slot x),
      let e := (R.births path w).job.immutable.payload.payload
      ∀ y∈e.pages,(originPayload y.payload).length≤pageBound) :
    let run := nativeStream (canonicalStreaming R) retire r .root initial
    (T.frame (NativeReach.reflexive r)).decode run.result.1=(sourceBlueprint sel r hf).program.run r ∧
    run.result.2=initial ∧
      ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x),
        ∃ m n,JointSuspensions (canonicalStreaming R) retire initial p m n ∧
          residentAtlasBits (stackBank R.births initial p)+m+n≤
            absoluteSelectedRoof (s:=s) (C:=C) initial r.edges r.prec pageBound := by
  obtain ⟨v,ret⟩ := canonical_whole_stream R retire initial origin legal
  exact ⟨v,ret,fun p => actual_absolute_path_selected_peak R retire initial qFit pageBound rows bits p⟩

#print axioms absolute_ancestral_numeric_and_mode_bits
#print axioms actual_absolute_path_selected_peak
#print axioms actual_absolute_source_value_and_selected_peak
end J6R50Peak
