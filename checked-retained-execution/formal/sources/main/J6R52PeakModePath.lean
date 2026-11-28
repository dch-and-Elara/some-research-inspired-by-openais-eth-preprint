
import J6R52PeakMode
import J6R50PeakAbsoluteCaps

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

def storedModeWeights (o : NativeSuspension (C:=C) (sel:=sel) c) : List Bool :=
  o.input.words.flatMap Word.bits

theorem fixed_weight_words_width {q' : ℕ} (words : List (Word q')) :
    (words.flatMap Word.bits).length=words.length*q' := by
  induction words with
  | nil => simp
  | cons w tail ih =>
    rw [List.flatMap_cons,List.length_append,w.size,ih,List.length_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm]

def weightCap (s C low : ℕ) : ℕ :=
  (6*(C*s)*low)*uniformWidth s C

theorem actual_site_weight_bits (T : Prepared cfg sel r hf) (p : Path sel r c)
    (o : NativeSuspension (C:=C) (sel:=sel) c) :
    (storedModeWeights o).length≤weightCap s C (absolutePrecision s r.edges r.prec) := by
  letI : Fintype c.host.Edge := c.host.finiteEdge
  have hE : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact o.ready.edgeCount
  have lo := absolute_register_precision_cap cfg sel T.rootStable p o.ready.active o.center
  have m := actual_edges_uniform T p
  have shape := physical_roster_length (packing sel o.ready) (centerIndex o.ready o.center)
    o.input.modes o.input.nodup o.input.allModes
  rw [hE] at shape
  have e := congrArg List.length o.input.weightMeaning
  simp only [List.length_map] at e
  rw [storedModeWeights,fixed_weight_words_width,e]
  unfold weightCap
  exact Nat.mul_le_mul (shape.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ m) lo)) o.fitsWord

inductive OnlineModePath (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ → Prop where
  | root : OnlineModePath M retire initial (.root : Path sel r r) 0
  | enter {x : Call (PhysicalHost f ell)} {p : Path sel r x} {b : ℕ}
      (prior : OnlineModePath M retire initial p b)
      (w : (P).Slot x) (o : NativeSuspension (C:=C) (sel:=sel) x)
      (event : SawOnlineMode M retire initial p w o) :
      OnlineModePath M retire initial (.step p w)
        (b+(o.measure.bits+(storedModeWeights o).length))

theorem every_actual_online_path_tracks_modes
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (qFit : q≤uniformWidth s C) (p : Path sel r c) :
    ∃ b,OnlineModePath M retire initial p b := by
  induction p with
  | root => exact ⟨0,.root⟩
  | step p w ih =>
    obtain ⟨b,earlier⟩ := ih
    obtain ⟨o,seen⟩ := each_online_slot_has_its_real_mode_event M retire initial qFit p w
    exact ⟨_,.enter earlier w o seen⟩

theorem actual_online_path_tracks_mode_bit_bound
    {M : OnlineMachine T key prec tw bw page q} {retire : J→ℕ} {initial : L}
    {p : Path sel r c} {b : ℕ} (trace : OnlineModePath M retire initial p b) :
    let low := absolutePrecision s r.edges r.prec
    b≤pathLimit s C*(absoluteModeCap s C ell f.natDegree low+weightCap s C low) := by
  let low := absolutePrecision s r.edges r.prec
  let A := absoluteModeCap s C ell f.natDegree low+weightCap s C low
  have counted : b≤moves p*A := by
    induction trace with
    | root => simp [moves]
    | @enter x p b prior w o event ih =>
      have m := mode_selected_payload_absolute T p o
      have wB := actual_site_weight_bits T p o
      simp only [moves,Nat.add_mul,Nat.one_mul]
      exact Nat.add_le_add ih (Nat.add_le_add m wB)
  exact counted.trans (Nat.mul_le_mul_right _ (actual_ancestry_moves_any_start cfg sel T.rootStable p))

#print axioms fixed_weight_words_width
#print axioms every_actual_online_path_tracks_modes
#print axioms actual_online_path_tracks_mode_bit_bound
#print axioms actual_site_weight_bits
end J6R52Peak
