import A1R43LiteralLayout
import A1R43LiteralEstimate
import A1R43LiteralSchedule
import A1R43LiteralGate
import A1R43LiteralShift
import J6R12RepackProvider
import J6R12BlueprintReach

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13000000
set_option maxRecDepth 1900

/-! The real binary source star host is active at its printed root.
Install the exact fully occupied packing and keep it in the selected
root; only genuine descendants are assigned fresh ordinary layouts. -/
namespace A1R43Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R11Repack J6R12Repack J6R12Blueprint J6ActiveRun
open J6ActiveSchedule J6R11Blueprint J1PPrinted J6R11Threshold P1DyadicGrid P11FullPacking
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (F : Finset (V×V))
local notation "m" => Nat.card (Occ F)
local notation "s" => starSize m
local notation "WPlan" => PairPlan F (smallA m) (copies m)
variable (W : PairPlan F (smallA (Nat.card (Occ F))) (copies (Nat.card (Occ F))))
local notation "Pad" => Spare F W
local notation "N" => network F Pad
variable (f : ℤ[X])
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s

theorem legal_plan_exists (cubic : ∀ v,GraphCutMoments.degree F v=3)
    (guard : PrintedMargins m) : Nonempty WPlan := by
  obtain ⟨rs,cs,_hv,cap⟩ := A2_chosen_simulation_capacity F cubic (smallA m)
    (copies m * 2^smallA m) guard.collision_A2 guard.paired_capacity
  exact ⟨⟨0,rs,cs,cap⟩⟩

def starFillFinite : Fintype (Spare F W) := Fintype.ofFinite (Spare F W)

include W in
def starRoot : Call (PhysicalHost f 1) := by
  letI : Fintype (Spare F W) := starFillFinite F W
  let h : PhysicalHost f 1 :=
    physicalHost (network F (Spare F W)) (@A1R43Literal.file V (Spare F W) inferInstance F f (Fintype.card V+1))
  exact ⟨h,0,h.edgeCount,Fintype.card V+1⟩

theorem star_root_creation :
    GoodTags (starRoot F W f).host (starRoot F W f).prec := by
  intro r
  exact le_rfl

theorem star_root_degree (cubic : ∀ v,GraphCutMoments.degree F v=3) :
    GoodDegree (starRoot F W f).host 3 := by
  constructor
  · intro r
    change Nat.card {w : Wire F Pad//(N).row w=r}≤3
    rcases r with r|z
    · rw [real_row_degree]
      decide
    · let h : {w : Wire F Pad//(N).row w=.inr z} ↪ Unit :=
        ⟨fun _=>(),fun x y _=>Subtype.ext
          (((dummy_row_unique F Pad z x.val).1 x.property).trans
            ((dummy_row_unique F Pad z y.val).1 y.property).symm)⟩
      exact (Nat.card_le_card_of_injective h h.injective).trans (by simp)
  · intro c
    change Nat.card {w : Wire F Pad//(N).col w=c}≤3
    rcases c with v|z
    · rw [real_column_degree,cubic]
    · let h : {w : Wire F Pad//(N).col w=.inr z} ↪ Unit :=
        ⟨fun _=>(),fun x y _=>Subtype.ext
          (((dummy_col_unique F Pad z x.val).1 x.property).trans
            ((dummy_col_unique F Pad z y.val).1 y.property).symm)⟩
      exact (Nat.card_le_card_of_injective h h.injective).trans (by simp)

theorem root_wire_count (guard : PrintedMargins m) :
    (starRoot F W f).edges=floorWires m := by
  change (starRoot F W f).host.edgeCount = _
  rw [←host_card]
  change Nat.card (Wire F Pad) = _
  rw [full_wire_count,lower_word_cell_count,guard.full_dim]
  rfl

theorem root_bits (guard : PrintedMargins m) :
    (S).levelBits (starRoot F W f).depth=smallA m+1 := by
  change stepA (Nat.clog 2 s) 0 = _
  rw [source_dim_zero,guard.full_dim]

theorem root_degrees_source (guard : PrintedMargins m) (cubic : ∀ v,GraphCutMoments.degree F v=3) :
    GoodDegree (starRoot F W f).host Δ := by
  obtain ⟨a,b⟩ := star_root_degree F W f cubic
  exact ⟨fun x=>(a x).trans guard.local_degree,fun y=>(b y).trans guard.local_degree⟩

theorem star_stable (guard : PrintedMargins m) (cubic : ∀ v,GraphCutMoments.degree F v=3) :
    Stable s 1 (starRoot F W f) := by
  refine stable_root s 1 _ rfl rfl (root_degrees_source F W f guard cubic) (star_root_creation F W f) ?_
  rw [root_wire_count F W f guard,one_mul]
  exact guard.wire_window.2

theorem star_ready (guard : PrintedMargins m) (cubic : ∀ v,GraphCutMoments.degree F v=3)
    (hF : f.natDegree=4*Nat.clog 2 s) (large : (2*epsDen)^30*(1:ℕ)^10≤Nat.clog 2 s) :
    Ready S Δ (starRoot F W f) := by
  have ht := printed_size_implies_numeric_guards s 1 (by decide) large
  have ha : (S).cutoff<(starRoot F W f).edges := by
    change J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)<(starRoot F W f).edges
    rw [root_wire_count F W f guard]
    exact guard.active_half.trans_le guard.wire_window.1
  have hsz : 8^(starRoot F W f).depth*(starRoot F W f).edges≤1*s := by
    change 1*(starRoot F W f).edges≤1*s
    rw [root_wire_count F W f guard,one_mul,one_mul]
    exact guard.wire_window.2
  exact ready_of_size s 1 _ (by decide) ht.2.1 hF guard.u_pos large ha hsz rfl
    (root_degrees_source F W f guard cubic) (star_root_creation F W f)

def castSelected {H : PhysicalHost f 1} {a a' : ℕ} (eq : a=a')
    (P : Selected H a (Fin 64)) : Selected H a' (Fin 64) :=
  eq ▸ P

theorem selected_predecessor_cast {H : PhysicalHost f 1} {a a' : ℕ} (eq : a=a')
    (P : Selected H a (Fin 64)) (r q : H.Edge) (h : unitPredecessor P.packing r q) :
    unitPredecessor (castSelected f eq P).packing r q := by subst a'; exact h

def starSelected (guard : PrintedMargins m) :
    Selected (starRoot F W f).host ((S).levelBits (starRoot F W f).depth) (Fin 64) :=
  castSelected f (root_bits F W f guard).symm ⟨fullPacking F W,full_minimum_rounded F W⟩

def starSelector (guard : PrintedMargins m) : Selector S Δ :=
  pinnedSelector S Δ (starRoot F W f) (starSelected F W f guard)

theorem same_selected_predecessor (guard : PrintedMargins m)
    (d : Ready S Δ (starRoot F W f)) (u : Occ F) :
    unitPredecessor (packing (starSelector F W f guard) d) (oddWire F Pad u) (evenWire F Pad u) := by
  rw [starSelector,pinned_at_root]
  exact selected_predecessor_cast f _ _ _ _ (full_seat_predecessor F W u)

def negativeCenter (guard : PrintedMargins m) : Center S (starRoot F W f) := by
  refine ⟨-1,?_⟩
  rw [J6ActiveSchedule.active,Finset.mem_filter]
  refine ⟨Finset.mem_erase.mpr ⟨by decide,minus_one_mem_grid _⟩,?_⟩
  have hu : 0<(S).levelWidth (starRoot F W f).depth := by
    change 0<stepU (Nat.clog 2 s) 0
    change 0<J9PrintedSchedule.rootU (Nat.clog 2 s)
    exact guard.u_pos
  have hM : 0<(starRoot F W f).edges := by
    rw [root_wire_count F W f guard]
    exact (Nat.zero_le _).trans_lt (guard.active_half.trans_le guard.wire_window.1)
  unfold J6ActiveSchedule.order
  have hv : padicValInt 2 (-1)=0 := by simp
  rw [hv,Nat.sub_zero]
  apply Nat.mul_pos _ hu
  unfold J6ActiveSchedule.height
  apply Nat.div_pos (by omega) hu

theorem negative_at_index_zero (guard : PrintedMargins m) (d : Ready S Δ (starRoot F W f)) :
    (centerIndex d (negativeCenter F W f guard)).val=0 := by
  change padicValInt 2 (-1)=0
  simp

#print axioms legal_plan_exists
#print axioms star_root_creation
#print axioms star_root_degree
#print axioms root_wire_count
#print axioms root_bits
#print axioms star_stable
#print axioms star_ready
#print axioms same_selected_predecessor
#print axioms negativeCenter
#print axioms negative_at_index_zero
end
end A1R43Literal
