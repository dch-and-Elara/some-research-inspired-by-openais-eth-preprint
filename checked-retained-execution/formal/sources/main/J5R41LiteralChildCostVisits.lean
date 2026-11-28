import J5R41LiteralChildCostGeometry
import J6R10RepackPrecision

/-! The same real tiles, matched positions and physical old vertices
determine the J5 visit and word counts. The layout geometry supplies
all packet, tile and feature bounds; only the original bounded old
tensor degree is a premise here. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open P11FullPacking J6R10Repack J6R9PacketScopes J6R9PacketTiles
open OuterNodePacking

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B]
    [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G)

def rowReal (x : Physical a P.copies G) : Bool :=
  decide (∃ e : E, P.seat e=x ∧ rowGroup P.mask i x=g)

def colReal (x : Physical a P.copies G) : Bool :=
  decide (∃ e : E, P.seat e=x ∧ colGroup P.mask i x=g)

/-- Only both occupied endpoints of a true shift at this child count
as matched; padding and outside-group ports are not Boolean states. -/
def matched (t : ℤ) : Finset (Physical a P.copies G) :=
  matchedColumns Finset.univ (rowReal P i g) (colReal P i g) t

theorem actual_match_count (t : ℤ) :
    (matched P i g t).card*2^a≤3*Nat.card E*(2^a-t.natAbs) := by
  have h := J45Cost.actual_matched_bound (Finset.univ : Finset (Page a P.copies G))
    (rowReal P i g) (colReal P i g) t
  rw [Finset.card_univ,←Nat.card_eq_fintype_card] at h
  calc
    _≤(Nat.card (Page a P.copies G)*(2^a-t.natAbs))*2^a :=
      Nat.mul_le_mul_right _ h
    _=(Nat.card (Page a P.copies G)*2^a)*(2^a-t.natAbs) := by ac_rfl
    _≤_ := Nat.mul_le_mul_right _ (source_pages_limit P)

theorem outer_match_count (t : ℤ) (houter : t.natAbs=2^a-1) :
    (matched P i g t).card*2^a≤3*Nat.card E := by
  have h : 2^a-t.natAbs=1 := by
    have hp : 0<(2:ℕ)^a := by positivity
    omega
  simpa only [h,mul_one] using actual_match_count P i g t

abbrev ColVertex := {b : B // P.colLabel b i=g}
abbrev ColPort (b : ColVertex P i g) := {e : E // N.col e=b.val}
abbrev RowVertex := {b : A // P.rowLabel b i=g}
abbrev RowPort (b : RowVertex P i g) := {e : E // N.row e=b.val}

variable {p : ℕ}

def tileWires (k : Tile P i) : Finset E :=
  Finset.univ.filter (fun e=>tileOf P i e=k)

/-- H_{tau,b}, computed over the actual occupied columns and the
actual within-tile quotient j. The one factor at j=0,b=0 is 1. -/
def H (m : Mode i p P.mask) : ℕ :=
  ∑ e∈tileWires P i (modeTile P i m), (ordinal P i e).val^m.order.val

theorem tileWires_card (k : Tile P i) : (tileWires P i k).card≤tileLen i := by
  have h := real_tile_card P i k
  rw [←tileLen_eq_half] at h
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at h
  exact h

theorem actual_increment_range (bmax : ℕ) (m : Mode i p P.mask) (h : m.order.val≤bmax) :
    H P i m≤(tileLen i)^(bmax+1) := by
  unfold H
  let K := tileLen i
  let F := tileWires P i (modeTile P i m)
  change ∑ e∈F,(ordinal P i e).val^m.order.val≤_
  calc
    _≤∑ e∈F,K^bmax := by
      refine Finset.sum_le_sum fun e _=>?_ 
      exact (pow_le_pow_left' (Nat.le_of_lt (ordinal P i e).isLt) _).trans
        (Nat.pow_le_pow_right (tileLen_pos i) h)
    _=F.card*K^bmax := by simp
    _≤K*K^bmax := Nat.mul_le_mul_right _ (tileWires_card P i _)
    _=_ := by rw [pow_succ,mul_comm]

variable (req : Finset (Mode i p P.mask))

abbrev Axis := ↥req
abbrev spanAt (u : Axis P i req) := H P i u.val

def V : ℕ := ∏ u : Axis P i req, (spanAt P i req u+1)

theorem requested_mode_count (bmax : ℕ)
    (ok : ∀ m ∈ req,source P.mask i m=g ∧ m.order.val≤bmax) :
    req.card≤Nat.card (Tile P i)*(bmax+1) := by
  let incl : Axis P i req→shortModes (p:=p) P i g bmax := fun m=>⟨m.val,ok m.val m.prop⟩
  have inj : Function.Injective incl := by
    intro x y h
    exact Subtype.ext (congrArg (fun j : shortModes (p:=p) P i g bmax=>j.val) h)
  have h := Nat.card_le_card_of_injective _ ((shortModeChart (p:=p) P i g bmax).injective.comp inj)
  simpa only [Nat.card_eq_fintype_card (α:=Axis P i req),Fintype.card_coe,
    Nat.card_prod,Nat.card_fin] using h

theorem actual_volume_bound (bmax : ℕ)
    (ok : ∀ m ∈ req,source P.mask i m=g ∧ m.order.val≤bmax) :
    V P i req≤(tileLen i^(bmax+1)+1)^(Nat.card (Tile P i)*(bmax+1)) := by
  unfold V
  calc
    _≤∏ _u : Axis P i req,(tileLen i^(bmax+1)+1) := by
      refine Finset.prod_le_prod' (fun u _=> Nat.add_le_add_right
        (actual_increment_range P i bmax u.val (ok _ u.prop).2) _)
    _=(tileLen i^(bmax+1)+1)^req.card := by simp
    _≤_ := Nat.pow_le_pow_right (by positivity) (requested_mode_count P i g req bmax ok)

abbrev localColumnBits (b : ColVertex P i g) := ColPort P i g b→Bool

theorem parity_outer_exponent (t : ℤ) (houter : t.natAbs=2^a-1) (hodd : i.val=0) :
    ((matched P i g t).card + Fintype.card (Tile P i×Bool))*2^a≤15*Nat.card E := by
  have hf := source_two_feature_limit P i
  rw [Nat.card_eq_fintype_card] at hf
  have hD : D i = 2^a := by simp [D,hodd]
  rw [hD] at hf
  rw [Nat.add_mul]
  exact (Nat.add_le_add (outer_match_count P i g t houter) hf).trans (by omega)

#print axioms actual_match_count
#print axioms outer_match_count
#print axioms tileWires_card
#print axioms actual_increment_range
#print axioms requested_mode_count
#print axioms actual_volume_bound
#print axioms parity_outer_exponent
end
end J5R41LiteralChildCost