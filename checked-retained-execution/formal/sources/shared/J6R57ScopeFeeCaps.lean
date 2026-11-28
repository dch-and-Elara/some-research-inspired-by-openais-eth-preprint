import J6R57ScopeFeeSidecar
import J6R57ScopeFeePublication
import J6R55CachedLedgerCore

/-! Uniformize the structural part of actual acquisition using only
word widths, finite directory sizes, and the real parent-edge bound.
The boot, demand, and per-port query producer Meters are still charged. -/
namespace J6R57ScopeFee
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R11Blueprint J1PPrinted J6R16ModeCost
open J6R10Repack J6R24MeteredRecursion J6R34ChildPath
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS J6R50SourceProducer J6R50Peak J6R51Peak J6R51Online
open J6R36ChildFramedRoute J6R48RawRoute J6R41StructuredAllPaths J6R52Peak J6R52CacheWhole J6R53PeakAddon
open J6R55CachedLedger
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4800
set_option Elab.async false
noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

structure ScopeWordCaps where
  fixed : ℕ
  addr : ℕ
  seed : ℕ
  initialHeader : ℕ
  owner : ℕ
  ownerKey : ℕ
  seatKey : ℕ
  ownerRows : ℕ
  seatRows : ℕ

structure ScopeWordFits (M : OnlineMachine T key prec tw bw page q) (initial : L)
    (W : ScopeWordCaps) : Prop where
  entry : EntryWidths M W.fixed W.addr
  boot : BootBodyWidth M W.seed
  handles : OwnerWidth M W.owner
  headers : ∀ row∈initial.headers,row.bytes.length≤W.initialHeader
  lookup : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x)
    (u : (Plan sel).Slot x) (w : (Plan sel).Slot ((Plan sel).child x u)),
      let D := (M.demand (sourceState M p u) w).result.directory
      D.k1≤W.ownerKey ∧ D.k2≤W.seatKey ∧ D.owners.length≤W.ownerRows ∧ D.seats.length≤W.seatRows

def uniformIndexGeometry (s parentEdges key prec page : ℕ) (W : ScopeWordCaps) : ℕ :=
  4+2*parentEdges*(3*W.addr+11+maxAddonFee W.owner (Nat.clog 2 s) key prec page)

def uniformDescSidecar (s parentEdges key prec page : ℕ) (W : ScopeWordCaps) : ℕ :=
  sidecarGeometry parentEdges W.addr W.owner (Nat.clog 2 s) key prec page
    W.ownerKey W.seatKey W.ownerRows W.seatRows

theorem edge_width_of_actual_path (p : Path sel r c) : c.edges≤r.edges := by
  induction p with
  | root => exact Nat.le_refl _
  | step prev u ih => exact (Nat.le_of_lt ((Plan sel).smaller _ u)).trans ih

theorem locate_fee_mono_width_tables {k K n N : ℕ} (keyLe : k≤K) (lenLe : n≤N) :
    locateFee k n≤locateFee K N := by
  unfold locateFee
  exact Nat.add_le_add_right (Nat.mul_le_mul lenLe (by omega)) _

theorem actual_first_index_at_uniform_width
    (M : OnlineMachine T key prec tw bw page q) (initial : L)
    (W : ScopeWordCaps) (fits : ScopeWordFits M initial W) (w : (Plan sel).Slot r) :
    (sourceBankAt M .root w).steps≤uniformIndexGeometry s r.edges key prec page W := by
  let X := (M.initial w).result
  have raw : X.site.install.steps≤4+2*r.edges*(3*X.birth.port+11+
      maxAddonFee X.site.ownerWidth (dim ((Path.root : Path sel r r).ticket w)) key prec page) :=
    actual_physical_index_install_ceiling X.site
  have a := (fits.entry (Path.root : Path sel r r) w).2
  have b := fits.handles (Path.root : Path sel r r) w
  have d : dim ((Path.root : Path sel r r).ticket w)≤Nat.clog 2 s := bits_le_lam _ _
  change X.birth.port+6≤W.addr at a
  change X.site.ownerWidth≤W.owner at b
  change X.site.install.steps≤_
  unfold uniformIndexGeometry
  refine raw.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ ?_) _)
  unfold maxAddonFee
  omega

theorem actual_later_index_and_emit_at_uniform_width
    (M : OnlineMachine T key prec tw bw page q) (initial : L)
    (W : ScopeWordCaps) (fits : ScopeWordFits M initial W)
    (p : Path sel r c) (u : (Plan sel).Slot c) (w : (Plan sel).Slot ((Plan sel).child c u)) :
    let K := (M.demand (sourceState M p u) w).result
    K.sidecarCharge≤sidecarQueryBill K+uniformDescSidecar s r.edges key prec page W := by
  let X := sourceState M p u
  let K := (M.demand X w).result
  have a := (fits.entry (Path.step p u) w).2
  have h := fits.handles (Path.step p u) w
  change K.advance.next.birth.port+6≤W.addr at a
  change K.directory.ow≤W.owner at h
  have d : dim (successorTicket (p.ticket u) w)≤Nat.clog 2 s := bits_le_lam _ _
  obtain ⟨h1,h2,h3,h4⟩ := fits.lookup p u w
  have lk1 : locateFee K.directory.k1 K.directory.owners.length≤locateFee W.ownerKey W.ownerRows := locate_fee_mono_width_tables h1 h3
  have lk2 : locateFee K.directory.k2 K.directory.seats.length≤locateFee W.seatKey W.seatRows := locate_fee_mono_width_tables h2 h4
  have rowCount : 2*((Plan sel).child c u).edges≤2*r.edges := by
    exact Nat.mul_le_mul_left 2 (edge_width_of_actual_path (Path.step p u))
  change K.sidecarCharge≤_
  refine (actual_demand_sidecar_ceiling K).trans (Nat.add_le_add_left ?_ _)
  unfold uniformDescSidecar sidecarGeometry
  apply Nat.add_le_add_left
  apply Nat.mul_le_mul rowCount
  unfold maxAddonFee
  omega

end
#print axioms edge_width_of_actual_path
#print axioms locate_fee_mono_width_tables
#print axioms actual_first_index_at_uniform_width
#print axioms actual_later_index_and_emit_at_uniform_width
end J6R57ScopeFee
