
import J6R52PeakModePath
import J6R52PeakNumeric

/-! Same-path trace of both actual online arithmetic suspensions,
including the selected current weight tape which the probe cursor
and its continuation consume. No array of all trace prefixes runs. -/
namespace J6R52Peak
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49LiveBits J6R50Peak J6R51Online

set_option autoImplicit false
set_option maxRecDepth 3550
set_option maxHeartbeats 19000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page
local notation "P" => (Plan sel)

inductive OnlineTrace (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ → Prop where
  | root : OnlineTrace M retire initial (.root : Path sel r r) 0
  | enter {x : Call (PhysicalHost f ell)} {p : Path sel r x} {b : ℕ}
      (prior : OnlineTrace M retire initial p b)
      (w : (P).Slot x) (o : NativeSuspension (C:=C) (sel:=sel) x)
      (event : SawOnlineMode M retire initial p w o) (v : OnlineNumeric M p w) :
      OnlineTrace M retire initial (.step p w)
        (b+(o.measure.bits+(storedModeWeights o).length+(v.payload retire initial).length))

theorem every_actual_online_path_has_joint_trace
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (fits : q≤uniformWidth s C) (p : Path sel r c) :
    ∃ b,OnlineTrace M retire initial p b := by
  induction p with
  | root => exact ⟨0,.root⟩
  | step p w ih =>
    obtain ⟨b,earlier⟩ := ih
    obtain ⟨o,seen⟩ := each_online_slot_has_its_real_mode_event M retire initial fits p w
    obtain ⟨v⟩ := each_online_slot_has_the_native_numeric_pause M p w
    exact ⟨_,.enter earlier w o seen v⟩

def arithmeticFrameCap (s C ell e low high : ℕ) : ℕ :=
  absoluteModeCap s C ell e low+weightCap s C low+onlineNumericalCap s C ell e low high

theorem actual_online_ancestor_field_bound
    {M : OnlineMachine T key prec tw bw page q} {retire : J→ℕ} {initial : L}
    {p : Path sel r c} {b : ℕ} (trace : OnlineTrace M retire initial p b)
    (high : ℕ) (fit : ActualHighFit M high) :
    b≤pathLimit s C*arithmeticFrameCap s C ell f.natDegree (absolutePrecision s r.edges r.prec) high := by
  let A := arithmeticFrameCap s C ell f.natDegree (absolutePrecision s r.edges r.prec) high
  have tracked : b≤moves p*A := by
    induction trace with
    | root => simp [moves]
    | @enter x p b earlier w o event v ih =>
      have m := mode_selected_payload_absolute T p o
      have wB := actual_site_weight_bits T p o
      have n := actual_online_numeric_payload_cap v retire initial high fit
      have term :
          o.measure.bits+(storedModeWeights o).length+(v.payload retire initial).length≤A :=
        Nat.add_le_add (Nat.add_le_add m wB) n
      simp only [moves,Nat.add_mul,Nat.one_mul]
      exact Nat.add_le_add ih term
  exact tracked.trans (Nat.mul_le_mul_right _ (actual_ancestry_moves_any_start cfg sel T.rootStable p))

#print axioms every_actual_online_path_has_joint_trace
#print axioms actual_online_ancestor_field_bound
end J6R52Peak
