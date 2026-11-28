import J8Physical
import J8SourceMomentFactor

/-!
From the literal finite packets to the J8 algebra. The compiler chooses
the unique physical successor of the unique matched leg, then returns the
ordinary old-column port in the same child. There is no additional axiom
asserting a split into input-independent public/target baselines.
-/

namespace J8Physical

open scoped Classical BigOperators
noncomputable section

variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)

abbrev Hit (r : R) := {v : Bool × Wire R // Shift d (r,v.1) v.2}

theorem hits_subsingleton (e : EndpointSeating d) (r : R) :
    Subsingleton (Hit d r) := by
  constructor
  intro h k
  have hx : (r,h.1.1) = (r,k.1.1) := row_hit_unique d e h.2 k.2 rfl
  have hy : h.1.2 = k.1.2 := by
    apply successor_unique d h.2
    rw [hx]
    exact k.2
  exact Subtype.ext (Prod.ext (congrArg Prod.snd hx) hy)

def actualHit (r : R) : Option (Hit d r) :=
  if h : Nonempty (Hit d r) then some h.some else none

theorem actualHit_some (e : EndpointSeating d) {r : R} {b : Bool} {y : Wire R}
    (h : Shift d (r,b) y) :
    actualHit d r = some ⟨(b,y),h⟩ := by
  have hn : Nonempty (Hit d r) := ⟨⟨(b,y),h⟩⟩
  letI : Subsingleton (Hit d r) := hits_subsingleton d e r
  rw [actualHit, dif_pos hn, Subsingleton.elim hn.some ⟨(b,y),h⟩]

def hitColumn (e : EndpointSeating d) {r : R} (h : Hit d r) : Sigma P :=
  (hit_is_nonpin d e h.2).choose

theorem hitColumn_eq (e : EndpointSeating d) {r : R} (h : Hit d r) :
    d.column h.1.2 = Sum.inr (hitColumn d e h) :=
  (hit_is_nonpin d e h.2).choose_spec

abbrev LocalRow (g : G) := {r : R // d.rowLabel r = g}
abbrev LocalColumn (g : G) := {v : V // d.colLabel v = g}
abbrev LocalPort {g : G} (v : LocalColumn d g) := P v.1

/-- Group membership of the selected original nonpin column is forced by
the packet orientation at the outer node. -/
theorem hitColumn_local (e : EndpointSeating d) (even : Even L)
    {g : G} (r : LocalRow d g) (h : Hit d r.1) :
    d.colLabel (hitColumn d e h).1 = g := by
  have same := shift_stays_in_child d even h.2
  rw [actualColLabel, hitColumn_eq] at same
  exact same.symm.trans r.2

def localAddress (e : EndpointSeating d) (even : Even L)
    {g : G} (r : LocalRow d g) (h : Hit d r.1) :
    Bool × (Sigma (LocalPort d (g := g))) :=
  (h.1.1, ⟨⟨(hitColumn d e h).1, hitColumn_local d e even r h⟩, (hitColumn d e h).2⟩)

def localHit (e : EndpointSeating d) (even : Even L) {g : G} (r : LocalRow d g) :
    Option (Bool × (Sigma (LocalPort d (g := g)))) :=
  (actualHit d r.1).map (localAddress d e even r)

def recoverWire {g : G} (p : Sigma (LocalPort d (g := g))) : Wire R :=
  d.column.symm (Sum.inr ⟨p.1.1, p.2⟩)

theorem recoverWire_address (e : EndpointSeating d) (even : Even L)
    {g : G} (r : LocalRow d g) (h : Hit d r.1) :
    recoverWire d (localAddress d e even r h).2 = h.1.2 := by
  unfold recoverWire
  change d.column.symm (Sum.inr (hitColumn d e h)) = _
  rw [← hitColumn_eq d e h, d.column.symm_apply_apply]

/-- All genuine hits are returned by the local wiring at that row. -/
theorem localHit_complete (e : EndpointSeating d) (even : Even L)
    {g : G} (r : LocalRow d g) {b : Bool} {y : Wire R}
    (h : Shift d (r.1,b) y) :
    (localHit d e even r).map (fun p => (p.1,recoverWire d p.2)) = some (b,y) := by
  simp only [localHit, actualHit_some d e h, Option.map_some, recoverWire_address]
  rfl

/-- Conversely, the compiled local table never invents a physical edge or
an additional matched leg. -/
theorem localHit_sound (e : EndpointSeating d) (even : Even L)
    {g : G} (r : LocalRow d g) {p : Bool × (Sigma (LocalPort d (g := g)))}
    (h : localHit d e even r = some p) : Shift d (r.1,p.1) (recoverWire d p.2) := by
  obtain ⟨u,hu,hp⟩ := Option.map_eq_some_iff.mp h
  subst p
  rw [recoverWire_address]
  exact u.2

theorem recoverWire_column {g : G} (p : Sigma (LocalPort d (g := g))) :
    d.column (recoverWire d p) = Sum.inr ⟨p.1.1,p.2⟩ :=
  d.column.apply_symm_apply _

theorem recoverWire_owner {g : G} (p : Sigma (LocalPort d (g := g))) :
    colOwner d (recoverWire d p) = Sum.inr p.1.1 := by
  simp [colOwner, recoverWire_column]

/-- A finite optional incidence lookup is converted to the exact input
type of the source/target local-mass compiler. -/
def wiringOfOption {A B : Type*} {Q : B → Type*}
    (h : A → Option (Bool × Sigma Q)) : J8SourceMoment.ColumnWiring A B Q where
  dest r := (h r).map (fun p => p.2.1)
  leg r := ((h r).map Prod.fst).getD false
  port _r _v hv :=
    let w := Option.map_eq_some_iff.mp hv
    w.choose_spec.2 ▸ w.choose.2.2

/-- Actual input for `J8SourceMoment.literalChild`, derived directly
from the supplied concrete physical packet placement. -/
def groupWiring (e : EndpointSeating d) (even : Even L) (g : G) :
    J8SourceMoment.ColumnWiring (LocalRow d g) (LocalColumn d g) (LocalPort d (g := g)) :=
  wiringOfOption (localHit d e even)

theorem wiringOfOption_read_none {A B : Type*} {Q : B → Type*}
    (h : A → Option (Bool × Sigma Q)) (r : A) (hr : h r = none) :
    J8SourceMoment.wireHit (wiringOfOption h) r = none := by
  apply J8SourceMoment.wireHit_none
  simp [wiringOfOption, hr]

theorem wiringOfOption_read_some {A B : Type*} {Q : B → Type*}
    (h : A → Option (Bool × Sigma Q)) (r : A) (b : Bool) (p : Sigma Q)
    (hr : h r = some (b,p)) :
    J8SourceMoment.wireHit (wiringOfOption h) r =
      some (b, fun x => x p.1 p.2) := by
  let W := wiringOfOption h
  have hd : W.dest r = some p.1 := by simp [W, wiringOfOption, hr]
  have hl : W.leg r = b := by simp [W, wiringOfOption, hr]
  change J8SourceMoment.wireHit W r = _
  rw [J8SourceMoment.wireHit_some _ _ _ hd, hl]
  have hport : W.port r p.1 hd = p.2 := by
    let w := Option.map_eq_some_iff.mp hd
    have hc : w.choose = (b,p) := Option.some.inj (w.choose_spec.1.symm.trans hr)
    change (w.choose_spec.2 ▸ w.choose.2.2) = p.2
    have transport {x y : Sigma Q} (e : x = y) (e0 : x.1 = y.1) :
        (e0 ▸ x.2) = y.2 := by
      cases e
      rfl
    exact transport (congrArg Prod.snd hc) w.choose_spec.2
  rw [hport]

/-- In the compiler, no two different local rows read a single old
column vertex. This is stronger than mere absence of repeated ports. -/
theorem group_dest_at_most_one (e : EndpointSeating d) (even : Even L)
    {g : G} (v : LocalColumn d g) (r s : LocalRow d g)
    (hr : (groupWiring d e even g).dest r = some v)
    (hs : (groupWiring d e even g).dest s = some v) : r = s := by
  obtain ⟨p,hp,hpv⟩ := Option.map_eq_some_iff.mp hr
  obtain ⟨q,hq,hqv⟩ := Option.map_eq_some_iff.mp hs
  have rp := localHit_sound d e even r hp
  have sq := localHit_sound d e even s hq
  have he : recoverWire d p.2 = recoverWire d q.2 := by
    apply column_hit_unique d e rp sq
    rw [recoverWire_owner, recoverWire_owner, hpv, hqv]
  rw [he] at rp
  exact Subtype.ext (congrArg Prod.fst (predecessor_unique d rp sq))

variable [Fintype R] [DecidableEq R] [DecidableEq Packet] [DecidableEq G]

/-- The literal finite set to pass as `s` to `completedTile` for this pin
tile. The group is read from the opposite end of the same pin wire. -/
def groupedTargets (p : S) : Finset (LocalRow d (d.rowLabel (pinWire d p).1) × Bool) :=
  Finset.univ.filter fun x => (x.1.1,x.2) ∈ targets d (pinWire d p)

theorem groupedTargets_nonempty (p : S)
    (off : d.rowLabel (pinWire d p).1 ≠ d.pinLabel p) :
    (groupedTargets d p).Nonempty := by
  refine ⟨(⟨(pinWire d p).1,rfl⟩, (pinWire d p).2), ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, pinWire_is_target d p off⟩

theorem groupedTargets_denom (p : S) (even : Even L) (size : 2 < L)
    {q : LocalRow d (d.rowLabel (pinWire d p).1) × Bool}
    (hq : q ∈ groupedTargets d p) :
    0 < (L:ℤ) - 1 - ((d.seat (pinWire d p)).2.val % 2 : ℕ) + (d.seat (q.1.1,q.2)).2.val ∧
      Odd ((L:ℤ) - 1 - ((d.seat (pinWire d p)).2.val % 2 : ℕ) + (d.seat (q.1.1,q.2)).2.val) :=
  every_target_positive_odd_denom d even size ((Finset.mem_filter.mp hq).2)

#print axioms hits_subsingleton
#print axioms hitColumn_local
#print axioms localHit_complete
#print axioms localHit_sound
#print axioms wiringOfOption_read_some
#print axioms group_dest_at_most_one
#print axioms groupedTargets_nonempty
#print axioms groupedTargets_denom

end
end J8Physical
