import A2R45LiteralDirectPacked
import A2R45LiteralAdmission
import J6R12Bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13500000
set_option synthInstance.maxHeartbeats 160000
set_option maxRecDepth 2350
set_option linter.unusedSectionVars false

/-! Root admission for the *direct* A2 path file, with the source full
packing, printed dimensions, t=-1, and P0=n+1. This does not charge
a uniform layout constructor or generate the marked slot replies. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial Std.Sat J7R9Compiler
open A1R43Literal A1R43Literal.General J6R10Repack J6R11Repack J6R12Repack J6R12Blueprint
open J6ActiveRun J6ActiveSchedule J6R11Blueprint J1PPrinted J6R11Threshold P1DyadicGrid P11FullPacking

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] (F : CNF V)
variable {Pad : Type}
local notation "U" => DirectWire F
local notation "R" => DirectRow F
local notation "C" => DirectCol F
local notation "E" => SplitWire U Pad
local notation "N" => directPhysical (Pad:=Pad) F

private def directOldRowMap (r : R) (e : {u : U//(directNetwork F).row u=r}) :
    {u : E//(N).row u=.inl r} := ⟨oddWire U Pad e.val,congrArg Sum.inl e.property⟩
private def directOldColMap (c : C) (e : {u : U//(directNetwork F).col u=c}) :
    {u : E//(N).col u=.inl c} := ⟨evenWire U Pad e.val,congrArg Sum.inl e.property⟩

private theorem directOldRowBij (r : R) : Function.Bijective (directOldRowMap (Pad:=Pad) F r) := by
  constructor
  · intro a b h
    exact Subtype.ext (congrArg Prod.fst (Sum.inl.inj (congrArg Subtype.val h)))
  · rintro ⟨⟨u,b⟩|z,h⟩
    · cases b
      · cases h
      · exact ⟨⟨u,Sum.inl.inj h⟩,rfl⟩
    · cases h

private theorem directOldColBij (c : C) : Function.Bijective (directOldColMap (Pad:=Pad) F c) := by
  constructor
  · intro a b h
    exact Subtype.ext (congrArg Prod.fst (Sum.inl.inj (congrArg Subtype.val h)))
  · rintro ⟨⟨u,b⟩|z,h⟩
    · cases b
      · exact ⟨⟨u,Sum.inl.inj h⟩,rfl⟩
      · cases h
    · cases h

def directDummyRowIndex : U⊕Pad→E
  | .inl u=>evenWire U Pad u
  | .inr p=>.inr p

private theorem directDummyRow_unique (u : E) (z : U⊕Pad) (h : (N).row u=.inr z) :
    u=directDummyRowIndex F z := by
  rcases u with ⟨u,b⟩|p
  · cases b
    · have eq : Sum.inl u=z := Sum.inr.inj h
      cases eq
      rfl
    · cases h
  · have eq : Sum.inr p=z := Sum.inr.inj h
    cases eq
    rfl

private theorem directDummyCol_unique (u : E) (z : U⊕Pad) (h : (N).col u=.inr z) :
    u=directDummyIndex F z := by
  rcases u with ⟨u,b⟩|p
  · cases b
    · cases h
    · have eq : Sum.inl u=z := Sum.inr.inj h
      cases eq
      rfl
  · have eq : Sum.inr p=z := Sum.inr.inj h
    cases eq
    rfl

theorem direct_physical_degree (width : ∀ cl∈F,cl.length≤3) :
    (∀ r,Nat.card {e : E//(N).row e=r}≤6) ∧
    (∀ c,Nat.card {e : E//(N).col e=c}≤3) := by
  obtain ⟨row,col⟩ := direct_concrete_network_degrees F width
  constructor
  · rintro (r|z)
    · rw [←Nat.card_congr (Equiv.ofBijective (directOldRowMap F r) (directOldRowBij F r))]
      exact row r
    · exact (Nat.card_le_card_of_injective (fun _ : {e : E//(N).row e=.inr z}=>())
        (fun x y _=>Subtype.ext ((directDummyRow_unique F x.val z x.property).trans
            (directDummyRow_unique F y.val z y.property).symm))).trans (by simp)
  · rintro (c|z)
    · rw [←Nat.card_congr (Equiv.ofBijective (directOldColMap F c) (directOldColBij F c))]
      exact col c
    · exact (Nat.card_le_card_of_injective (fun _ : {e : E//(N).col e=.inr z}=>())
        (fun x y _=>Subtype.ext ((directDummyCol_unique F x.val z x.property).trans
            (directDummyCol_unique F y.val z y.property).symm))).trans (by simp)

variable (W : DirectPlan F) (f : ℤ[X])
local notation "m" => directM F
local notation "s" => starSize m
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s

def directRoot : Call (PhysicalHost f 1) :=
  letI : Fintype (DirectPad F W) := directPadFinite F W
  let h := physicalHost (directPhysical (Pad:=DirectPad F W) F)
    (directNativeFile F f (Fintype.card V+1))
  ⟨h,0,h.edgeCount,Fintype.card V+1⟩

local notation "root" => directRoot F W f

theorem direct_root_wire_count (guard : PrintedMargins m) : (root).edges=floorWires m := by
  letI : Fintype (DirectPad F W) := directPadFinite F W
  change Fintype.card (SplitWire U (DirectPad F W))=_
  rw [←Nat.card_eq_fintype_card,full_wire_count,lower_word_cell_count,guard.full_dim]
  rfl

theorem direct_root_bits (guard : PrintedMargins m) : (S).levelBits (root).depth=smallA m+1 := by
  change stepA (Nat.clog 2 s) 0=_
  rw [source_dim_zero,guard.full_dim]

theorem direct_root_degree (width : ∀ cl∈F,cl.length≤3) (guard : PrintedMargins m) :
    GoodDegree (root).host Δ := by
  obtain ⟨vr,vc⟩ := direct_physical_degree (Pad:=DirectPad F W) F width
  exact ⟨fun r=>(vr r).trans (source_delta_ge_six m guard),
    fun c=>(vc c).trans ((by decide : 3≤6).trans (source_delta_ge_six m guard))⟩

theorem direct_root_tags : GoodTags (root).host (root).prec := by
  intro i
  exact le_rfl

theorem direct_root_stable (width : ∀ cl∈F,cl.length≤3) (guard : PrintedMargins m) :
    Stable s 1 root := by
  refine stable_root s 1 _ rfl rfl (direct_root_degree F W f width guard)
    (direct_root_tags F W f) ?_
  rw [direct_root_wire_count F W f guard,one_mul]
  exact guard.wire_window.2

theorem direct_root_ready (width : ∀ cl∈F,cl.length≤3) (guard : PrintedMargins m)
    (cfg : RootBounds s 1 f) : @J6R12Blueprint.Ready f 1 S Δ root := by
  have ha : (S).cutoff<(root).edges := by
    change J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)<(root).edges
    rw [direct_root_wire_count F W f guard]
    exact guard.active_half.trans_le guard.wire_window.1
  have hsz : 8^(root).depth*(root).edges≤1*s := by
    change 1*(root).edges≤1*s
    rw [direct_root_wire_count F W f guard,one_mul,one_mul]
    exact guard.wire_window.2
  exact ready_of_size s 1 _ cfg.constPos cfg.constSmall cfg.coefficient cfg.widthPos cfg.size ha hsz rfl
    (direct_root_degree F W f width guard) (direct_root_tags F W f)

def directSelected (guard : PrintedMargins m) :
    Selected (root).host ((S).levelBits (root).depth) (Fin 64) :=
  castSelected f (direct_root_bits F W f guard).symm
    ⟨fullPacking (directNetwork F) W,full_minimum_rounded (directNetwork F) W⟩

def directSelector (guard : PrintedMargins m) : Selector S Δ :=
  pinnedSelector S Δ root (directSelected F W f guard)

def directNegative (guard : PrintedMargins m) : Center S root := by
  refine ⟨-1,?_⟩
  rw [J6ActiveSchedule.active,Finset.mem_filter]
  refine ⟨Finset.mem_erase.mpr ⟨by decide,minus_one_mem_grid _⟩,?_⟩
  have hu : 0<(S).levelWidth (root).depth := by
    change 0<J9PrintedSchedule.rootU (Nat.clog 2 s)
    exact guard.u_pos
  have hm : 0<(root).edges := by
    rw [direct_root_wire_count F W f guard]
    exact (Nat.zero_le _).trans_lt (guard.active_half.trans_le guard.wire_window.1)
  unfold J6ActiveSchedule.order
  have hv : padicValInt 2 (-1)=0 := by simp
  rw [hv,Nat.sub_zero]
  apply Nat.mul_pos _ hu
  unfold J6ActiveSchedule.height
  apply Nat.div_pos (by omega) hu

theorem direct_negative_index (guard : PrintedMargins m) (d : @J6R12Blueprint.Ready f 1 S Δ root) :
    (centerIndex d (directNegative F W f guard)).val=0 := by
  change padicValInt 2 (-1)=0
  simp

theorem direct_root_selected_pair (guard : PrintedMargins m)
    (d : @J6R12Blueprint.Ready f 1 S Δ root) (u : U) :
    unitPredecessor (packing (directSelector F W f guard) d)
      (oddWire U (DirectPad F W) u) (evenWire U (DirectPad F W) u) := by
  rw [directSelector,pinned_at_root]
  exact selected_predecessor_cast f _ _ _ _ (full_seat_predecessor (directNetwork F) W u)

#print axioms direct_physical_degree
#print axioms direct_root_wire_count
#print axioms direct_root_bits
#print axioms direct_root_stable
#print axioms direct_root_ready
#print axioms direct_negative_index
#print axioms direct_root_selected_pair
end
end A2R45Literal
