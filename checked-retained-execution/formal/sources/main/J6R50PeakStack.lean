
import J6R50PeakFit
import J6R49DFSPathReach

/-! One same-path ledger for physical page frames, actual mode
suspensions, completed centre blocks, and paused interpolation jets.
Numbers in the trace are consequences of observed payload sizes.
This is not a count of all heap objects or the allocator workspace. -/
namespace J6R50Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS J6R49LiveBits

set_option autoImplicit false
set_option maxRecDepth 3300
set_option maxHeartbeats 17000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

inductive JointSuspensions (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ → ℕ → Prop where
  | root : JointSuspensions R retire initial (Path.root : Path sel r r) 0 0
  | push {x : Call (PhysicalHost f ell)} {p : Path sel r x} {m n : ℕ}
      (earlier : JointSuspensions R retire initial p m n)
      (w : (Plan sel).Slot x) (o : NativeSuspension (C:=C) (sel:=sel) x)
      (seen : ActualModeEvent R retire initial p w o) (view : NumericAt R p w) :
      JointSuspensions R retire initial (.step p w)
        (m+o.measure.bits) (n+(view.payload retire initial).length)

theorem joint_trace_projects_to_actual_modes
    {R : StreamingResident T key prec tw bw page q} {retire : J→ℕ} {initial : L}
    {p : Path sel r c} {m n : ℕ} (trace : JointSuspensions R retire initial p m n) :
    RecursiveModeTrace R retire initial p m := by
  induction trace with
  | root => exact .root
  | push _ w o seen _ ih => exact .push ih w o seen

theorem every_source_path_has_joint_suspensions
    (R : StreamingResident T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (qFit : q≤uniformWidth s C) (p : Path sel r c) :
    ∃ m n,JointSuspensions R retire initial p m n := by
  induction p with
  | root => exact ⟨0,0,.root⟩
  | step p w ih =>
    obtain ⟨m,n,trace⟩ := ih
    obtain ⟨o,seen⟩ := each_actual_slot_has_emission R retire initial qFit p w
    obtain ⟨E⟩ := actual_slot_has_numeric_pause R p w
    exact ⟨m+o.measure.bits,n+(E.payload retire initial).length,.push trace w o seen E⟩

theorem actual_numeric_ancestor_peak
    {R : StreamingResident T key prec tw bw page q} {retire : J→ℕ} {initial : L}
    {p : Path sel r c} {m n : ℕ} (trace : JointSuspensions R retire initial p m n)
    (d₀ : r.depth=0) (p₀ : r.prec≤C*s) (high : HighFit R) :
    n≤pathLimit s C*numericBase s C ell f.natDegree+
      (32*r.edges/29)*numericSlope s C ell f.natDegree := by
  let B := numericBase s C ell f.natDegree
  let A := numericSlope s C ell f.natDegree
  have track : n+c.edges*A≤moves p*B+(edgeStack p).sum*A := by
    induction trace with
    | root => simp [moves,edgeStack]
    | @push x p m n earlier w o seen E ih =>
      have field := actual_numeric_fields_affine E retire initial d₀ p₀ high
      change (E.payload retire initial).length≤B+x.edges*A at field
      simp only [moves,edgeStack,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.add_mul]
      omega
  have depth : moves p≤pathLimit s C := by
    have d := printed_stack_level_bound cfg T.rootStable d₀ p
    have H := (stack_exact_depth p).2
    omega
  have edges : (edgeStack p).sum≤32*r.edges/29 := by
    have e := edgeStack_geometric p
    omega
  exact (Nat.le_add_right _ _).trans (track.trans
    (Nat.add_le_add (Nat.mul_le_mul_right _ depth) (Nat.mul_le_mul_right _ edges)))

def selectedRoof (initial : L) (rootEdges pageBound : ℕ) : ℕ :=
  residentAtlasBits initial+(96*rootEdges/29)*(page+pageBound)+
    pathLimit s C*(frameBase (uniformWidth s C) (rosterSize s C)+numericBase s C ell f.natDegree)+
    (32*rootEdges/29)*(frameSlope s C ell f.natDegree+numericSlope s C ell f.natDegree)

theorem joint_scoped_selected_peak (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (p : Path sel r c)
    (m n : ℕ) (trace : JointSuspensions R retire initial p m n)
    (d₀ : r.depth=0) (p₀ : r.prec≤C*s) (high : HighFit R)
    (pageBound : ℕ) (rows : AllExactPages R.births)
    (bits : ∀ {x : Call (PhysicalHost f ell)} (path : Path sel r x) (w : (Plan sel).Slot x),
      let e := (R.births path w).job.immutable.payload.payload
      ∀ y∈e.pages,(originPayload y.payload).length≤pageBound) :
    residentAtlasBits (stackBank R.births initial p)+m+n≤
      selectedRoof (s:=s) (C:=C) initial r.edges pageBound := by
  have mode := combined_stream_selected_fields_peak R retire initial d₀ p₀ p m
    (joint_trace_projects_to_actual_modes trace) pageBound rows bits
  have num := actual_numeric_ancestor_peak trace d₀ p₀ high
  exact (Nat.add_le_add mode num).trans_eq (by unfold selectedRoof; ring)

#print axioms joint_trace_projects_to_actual_modes
#print axioms every_source_path_has_joint_suspensions
#print axioms actual_numeric_ancestor_peak
#print axioms joint_scoped_selected_peak
end J6R50Peak
