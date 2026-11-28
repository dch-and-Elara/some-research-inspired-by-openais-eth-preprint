
import A2R45LiteralDegrees
import A1R43LiteralGeneralEstimate
import A1R43LiteralShift
import J6R12RepackProvider
import J6R12BlueprintReach

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15000000
set_option maxRecDepth 1970
set_option linter.unusedSectionVars false

/-! Embed the same fully filled A2 topology at the actual printed active root.
The root label/seat plan is supplied once, independent of the switch tape.
The actual source-ready/capacity/center conditions are derived here. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R11Repack J6R12Repack J6R12Blueprint J6ActiveRun
open J6ActiveSchedule J6R11Blueprint J1PPrinted J6R11Threshold P1DyadicGrid P11FullPacking
open FixedHostAcquisition A1R43Literal A1R43Literal.General
noncomputable section

variable {n : ℕ}
abbrev simCount (n : ℕ) := Nat.card (Wire n)
local notation "m" => simCount n
local notation "s" => starSize m
abbrev Plan (n : ℕ) := General.PairPlan (simulated n) (smallA (simCount n)) (copies (simCount n))
variable (W : Plan n)
abbrev FilledPad : Type := General.Spare (simulated n) W
local notation "PP" => FilledPad W
local notation "Net" => nativeNetwork n PP
variable (w : Input n) (f : ℤ[X])
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s

theorem fixed_plan_exists (guard : PrintedMargins m) : Nonempty (Plan n) :=
  General.printed_general_pair_plan (simulated n) 4 guard (by decide)
    simulated_row_degrees (fun c=>(simulated_column_degrees c).trans (by decide))

def rootCall : Call (PhysicalHost f 1) :=
  ⟨physicalHost Net (file w f (n+2)),0,Fintype.card (NativeWire n PP),n+2⟩

theorem root_call_creation :
    GoodTags (rootCall W w f).host (rootCall W w f).prec := by
  intro r
  exact le_rfl

theorem root_call_degree : GoodDegree (rootCall W w f).host 4 := by
  constructor
  · intro r
    exact real_physical_row_degrees r
  · intro c
    exact (real_physical_col_degrees c).trans (by decide)

theorem root_wire_count (guard : PrintedMargins m) :
    (rootCall W w f).edges=floorWires m := by
  change Fintype.card (NativeWire n PP) = _
  rw [←Nat.card_eq_fintype_card,General.full_wire_count,lower_word_cell_count,guard.full_dim]
  rfl

theorem root_bits (guard : PrintedMargins m) :
    (S).levelBits (rootCall W w f).depth=smallA m+1 := by
  change stepA (Nat.clog 2 s) 0 = _
  rw [source_dim_zero,guard.full_dim]

theorem root_preview_degree (guard : PrintedMargins m) :
    GoodDegree (rootCall W w f).host Δ := by
  have hΔ : 4≤Δ := (by decide : 4≤6).trans (source_delta_ge_six m guard)
  obtain ⟨a,b⟩ := root_call_degree W w f
  exact ⟨fun x=>(a x).trans hΔ,fun y=>(b y).trans hΔ⟩

theorem root_stable (guard : PrintedMargins m) : Stable s 1 (rootCall W w f) := by
  refine stable_root s 1 _ rfl rfl (root_preview_degree W w f guard)
    (root_call_creation W w f) ?_
  rw [root_wire_count W w f guard,one_mul]
  exact guard.wire_window.2

theorem root_ready (guard : PrintedMargins m)
    (hF : f.natDegree=4*Nat.clog 2 s)
    (large : (2*epsDen)^30*(1:ℕ)^10≤Nat.clog 2 s) :
    Ready S Δ (rootCall W w f) := by
  have ht := printed_size_implies_numeric_guards s 1 (by decide) large
  have ha : (S).cutoff<(rootCall W w f).edges := by
    change J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)<(rootCall W w f).edges
    rw [root_wire_count W w f guard]
    exact guard.active_half.trans_le guard.wire_window.1
  have hsz : 8^(rootCall W w f).depth*(rootCall W w f).edges≤1*s := by
    change 1*(rootCall W w f).edges≤1*s
    rw [root_wire_count W w f guard,one_mul,one_mul]
    exact guard.wire_window.2
  exact ready_of_size s 1 _ (by decide) ht.2.1 hF guard.u_pos large ha hsz rfl
    (root_preview_degree W w f guard) (root_call_creation W w f)

def castSelected {H : PhysicalHost f 1} {a a' : ℕ} (eq : a=a')
    (P : Selected H a (Fin 64)) : Selected H a' (Fin 64) := eq ▸ P

theorem selected_predecessor_cast {H : PhysicalHost f 1} {a a' : ℕ} (eq : a=a')
    (P : Selected H a (Fin 64)) (r q : H.Edge) (h : unitPredecessor P.packing r q) :
    unitPredecessor (castSelected f eq P).packing r q := by subst a'; exact h

def fixedSelected (guard : PrintedMargins m) :
    Selected (rootCall W w f).host ((S).levelBits (rootCall W w f).depth) (Fin 64) :=
  castSelected f (root_bits W w f guard).symm
    ⟨General.fullPacking (simulated n) W,General.full_minimum_rounded (simulated n) W⟩

def fixedSelector (guard : PrintedMargins m) : Selector S Δ :=
  pinnedSelector S Δ (rootCall W w f) (fixedSelected W w f guard)

theorem same_selected_predecessor (guard : PrintedMargins m)
    (d : Ready S Δ (rootCall W w f)) (u : Wire n) :
    unitPredecessor (packing (fixedSelector W w f guard) d)
      (oddWire (Wire n) PP u) (evenWire (Wire n) PP u) := by
  rw [fixedSelector,pinned_at_root]
  exact selected_predecessor_cast f _ _ _ _ (General.full_seat_predecessor (simulated n) W u)

def negativeCenter (guard : PrintedMargins m) : Center S (rootCall W w f) := by
  refine ⟨-1,?_⟩
  rw [J6ActiveSchedule.active,Finset.mem_filter]
  refine ⟨Finset.mem_erase.mpr ⟨by decide,minus_one_mem_grid _⟩,?_⟩
  have hu : 0<(S).levelWidth (rootCall W w f).depth := by
    change 0<stepU (Nat.clog 2 s) 0
    change 0<J9PrintedSchedule.rootU (Nat.clog 2 s)
    have hu' := guard.u_pos
    omega
  have hM : 0<(rootCall W w f).edges := by
    rw [root_wire_count W w f guard]
    exact (Nat.zero_le _).trans_lt (guard.active_half.trans_le guard.wire_window.1)
  unfold J6ActiveSchedule.order
  have hv : padicValInt 2 (-1)=0 := by simp
  rw [hv,Nat.sub_zero]
  apply Nat.mul_pos _ hu
  unfold J6ActiveSchedule.height
  apply Nat.div_pos (by omega) hu

theorem negative_at_index_zero (guard : PrintedMargins m) (d : Ready S Δ (rootCall W w f)) :
    (centerIndex d (negativeCenter W w f guard)).val=0 := by
  change padicValInt 2 (-1)=0
  simp

#print axioms fixed_plan_exists
#print axioms root_call_creation
#print axioms root_call_degree
#print axioms root_wire_count
#print axioms root_bits
#print axioms root_preview_degree
#print axioms root_stable
#print axioms root_ready
#print axioms same_selected_predecessor
#print axioms negativeCenter
#print axioms negative_at_index_zero
end
end A2R45Literal
