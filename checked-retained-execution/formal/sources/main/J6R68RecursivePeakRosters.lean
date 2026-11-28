import J6R68RecursivePeakFields
import J6R57LiveSpaceCachedStack

/-! R57 counts the suspended cursor and weights, but cursor.n alone
is not the suspended roster. Separately charge the encoded keys of
the actual SiteTape.modes (and its independent precision word).
This is the same suspended input as SawCachedMode, not an outer
oracle's full catalogue or a fresh reconstruction. -/
namespace J6R68.RecursivePeak
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R17ModeTape
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49LiveBits
open J6R50SourceProducer J6R51Online J6R51Peak J6R52Peak J6R52CacheWhole J6R50Peak
open J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R66.BootPeak
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4430
set_option maxHeartbeats 17000000
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def suspendedRosterBits (o : NativeSuspension (C:=C) (sel:=sel) c) : ℕ :=
  bitSize (fun m=>modeRowBits (encodeMode (q:=o.q) (centerIndex o.ready o.center) m)) o.input.modes+
    o.input.precision.bits.length

def suspendedRosterCap (s C low : ℕ) : ℕ :=
  let W := uniformWidth s C
  let Λ := Nat.clog 2 s
  (6*(C*s))*low*(6*Λ+6*Λ+W+W+W)+W

theorem exact_suspended_site_roster_bits (o : NativeSuspension (C:=C) (sel:=sel) c) :
    let A := (S).levelBits c.depth
    suspendedRosterBits o=o.input.modes.length*(6*A+6*A+o.q+o.q+o.q)+o.q := by
  unfold suspendedRosterBits
  rw [o.input.precision.size,bitSize_exact _ _ _ (fun m=>real_mode_record_has_fixed_selected_width m)]

theorem actual_suspended_roster_has_absolute_selected_cap
    (T : Prepared cfg sel r hf) (p : Path sel r c)
    (o : NativeSuspension (C:=C) (sel:=sel) c) :
    suspendedRosterBits o≤suspendedRosterCap s C (absolutePrecision s r.edges r.prec) := by
  letI : Fintype c.host.Edge := c.host.finiteEdge
  have hE : Nat.card c.host.Edge=c.edges := by
    rw [Nat.card_eq_fintype_card]
    exact o.ready.edgeCount
  have lo := absolute_register_precision_cap cfg sel T.rootStable p o.ready.active o.center
  have m := actual_edges_uniform T p
  have shape := physical_roster_length (packing sel o.ready) (centerIndex o.ready o.center)
    o.input.modes o.input.nodup o.input.allModes
  rw [hE] at shape
  have n : o.input.modes.length≤(6*(C*s))*absolutePrecision s r.edges r.prec :=
    shape.trans (Nat.mul_le_mul (Nat.mul_le_mul_left _ m) lo)
  have ha : (S).levelBits c.depth≤Nat.clog 2 s := by
    simpa only [printedParams,printedShape] using bits_le_lam (Nat.clog 2 s) c.depth
  have weight : 6*(S).levelBits c.depth+6*(S).levelBits c.depth+o.q+o.q+o.q≤
      6*Nat.clog 2 s+6*Nat.clog 2 s+uniformWidth s C+uniformWidth s C+uniformWidth s C :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add
      (Nat.add_le_add (Nat.mul_le_mul_left 6 ha) (Nat.mul_le_mul_left 6 ha)) o.fitsWord)
      o.fitsWord) o.fitsWord
  rw [exact_suspended_site_roster_bits]
  exact Nat.add_le_add (Nat.mul_le_mul n weight) o.fitsWord

inductive ObservedRosterPause (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page) :
    {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ → ℕ → Prop where
  | root : ObservedRosterPause M retire initial (.root : Path sel r r) 0 0
  | step {x : Call (PhysicalHost f ell)} {p : Path sel r x} {bits roster : ℕ}
      (prior : ObservedRosterPause M retire initial p bits roster) (w : (@Plan f ell s sel).Slot x)
      (o : NativeSuspension (C:=C) (sel:=sel) x)
      (mode : SawCachedMode M retire initial p w o)
      (num : OnlineNumeric M p w) (visit : PaidBankVisit M retire initial p w) :
      ObservedRosterPause M retire initial (.step p w)
        (bits+(o.measure.bits+(storedModeWeights o).length+(cachedNumericPayload num retire initial).length))
        (roster+suspendedRosterBits o)

theorem same_actual_pauses_retain_the_actual_encoded_rosters
    {M : OnlineMachine T key prec tw bw page q} {retire : PageJob f ell key prec tw bw page→ℕ}
    {initial : PageBank f ell key prec tw bw page}
    {p : Path sel r c} {b : ℕ} (trace : CachedPausePath M retire initial p b) :
    ∃ k,ObservedRosterPause M retire initial p b k ∧
      k≤pathLimit s C*suspendedRosterCap s C (absolutePrecision s r.edges r.prec) := by
  let cap := suspendedRosterCap s C (absolutePrecision s r.edges r.prec)
  have one : ∃ k,ObservedRosterPause M retire initial p b k ∧ k≤moves p*cap := by
    induction trace with
    | root => exact ⟨0,.root,Nat.zero_le _⟩
    | @step x old used prior w o md num visit ih =>
      obtain ⟨k,retained,fit⟩ := ih
      refine ⟨k+suspendedRosterBits o,.step retained w o md num visit,?_⟩
      have localFit : suspendedRosterBits o≤cap := actual_suspended_roster_has_absolute_selected_cap T old o
      simpa only [moves,Nat.add_mul,Nat.one_mul] using Nat.add_le_add fit localFit
  obtain ⟨k,got,h⟩ := one
  exact ⟨k,got,h.trans (Nat.mul_le_mul_right _ (actual_ancestry_moves_any_start cfg sel T.rootStable p))⟩

#print axioms exact_suspended_site_roster_bits
#print axioms actual_suspended_roster_has_absolute_selected_cap
#print axioms same_actual_pauses_retain_the_actual_encoded_rosters
end
end J6R68.RecursivePeak