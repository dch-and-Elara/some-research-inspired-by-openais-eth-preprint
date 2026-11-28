import J8PhysicalWiring
set_option warningAsError true
namespace J8Physical.Relaxed
open scoped Classical BigOperators
noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)

/-- Only real initial rows need matching; last ports need not have distinct owners. -/
structure RowEndpointSeating where
  initialRows : ∀ x x' : Wire R, (d.seat x).2.val = 0 →
    (d.seat x').2.val = 0 → x.1 = x'.1 → x = x'
  finalNonpin : ∀ y : Wire R, (d.seat y).2.val = L-1 →
    ∃ v : Sigma P, d.column y = Sum.inr v

def weaken (e : EndpointSeating d) : RowEndpointSeating d where
  initialRows x x' hx hx' ho := e.rowMatching (e.chosen x (Or.inl hx)) (e.chosen x' (Or.inl hx')) ho
  finalNonpin y hy := e.nonpin y (e.chosen y (Or.inr hy))

theorem row_hit_unique (e : RowEndpointSeating d) {x x' y y' : Wire R}
    (h : Shift d x y) (h' : Shift d x' y') (owner : x.1 = x'.1) : x = x' :=
  e.initialRows x x' (shift_boundaries d h).1 (shift_boundaries d h').1 owner

theorem hit_is_nonpin (e : RowEndpointSeating d) {x y : Wire R} (h : Shift d x y) :
    ∃ v : Sigma P, d.column y = Sum.inr v :=
  e.finalNonpin y (shift_boundaries d h).2

theorem hits_subsingleton (e : RowEndpointSeating d) (r : R) :
    Subsingleton (Hit d r) := by
  constructor
  intro h k
  have hx : (r,h.1.1) = (r,k.1.1) := row_hit_unique d e h.2 k.2 rfl
  have hy : h.1.2 = k.1.2 := by
    apply successor_unique d h.2
    rw [hx]
    exact k.2
  exact Subtype.ext (Prod.ext (congrArg Prod.snd hx) hy)

theorem actualHit_some (e : RowEndpointSeating d) {r : R} {b : Bool} {y : Wire R}
    (h : Shift d (r,b) y) :
    actualHit d r = some ⟨(b,y),h⟩ := by
  have hn : Nonempty (Hit d r) := ⟨⟨(b,y),h⟩⟩
  letI : Subsingleton (Hit d r) := hits_subsingleton d e r
  rw [actualHit, dif_pos hn, Subsingleton.elim hn.some ⟨(b,y),h⟩]

def hitColumn (e : RowEndpointSeating d) {r : R} (h : Hit d r) : Sigma P :=
  (hit_is_nonpin d e h.2).choose

theorem hitColumn_eq (e : RowEndpointSeating d) {r : R} (h : Hit d r) :
    d.column h.1.2 = Sum.inr (hitColumn d e h) :=
  (hit_is_nonpin d e h.2).choose_spec


/-- Group membership of the selected original nonpin column is forced by
the packet orientation at the outer node. -/
theorem hitColumn_local (e : RowEndpointSeating d) (even : Even L)
    {g : G} (r : LocalRow d g) (h : Hit d r.1) :
    d.colLabel (hitColumn d e h).1 = g := by
  have same := shift_stays_in_child d even h.2
  rw [actualColLabel, hitColumn_eq] at same
  exact same.symm.trans r.2

def localAddress (e : RowEndpointSeating d) (even : Even L)
    {g : G} (r : LocalRow d g) (h : Hit d r.1) :
    Bool × (Sigma (LocalPort d (g := g))) :=
  (h.1.1, ⟨⟨(hitColumn d e h).1, hitColumn_local d e even r h⟩, (hitColumn d e h).2⟩)

def localHit (e : RowEndpointSeating d) (even : Even L) {g : G} (r : LocalRow d g) :
    Option (Bool × (Sigma (LocalPort d (g := g)))) :=
  (actualHit d r.1).map (localAddress d e even r)

theorem recoverWire_address (e : RowEndpointSeating d) (even : Even L)
    {g : G} (r : LocalRow d g) (h : Hit d r.1) :
    recoverWire d (localAddress d e even r h).2 = h.1.2 := by
  unfold recoverWire
  change d.column.symm (Sum.inr (hitColumn d e h)) = _
  rw [← hitColumn_eq d e h, d.column.symm_apply_apply]

/-- All genuine hits are returned by the local wiring at that row. -/
theorem localHit_complete (e : RowEndpointSeating d) (even : Even L)
    {g : G} (r : LocalRow d g) {b : Bool} {y : Wire R}
    (h : Shift d (r.1,b) y) :
    (localHit d e even r).map (fun p => (p.1,recoverWire d p.2)) = some (b,y) := by
  simp only [localHit, actualHit_some d e h, Option.map_some, recoverWire_address]
  rfl

/-- Conversely, the compiled local table never invents a physical edge or
an additional matched leg. -/
theorem localHit_sound (e : RowEndpointSeating d) (even : Even L)
    {g : G} (r : LocalRow d g) {p : Bool × (Sigma (LocalPort d (g := g)))}
    (h : localHit d e even r = some p) : Shift d (r.1,p.1) (recoverWire d p.2) := by
  obtain ⟨u,hu,hp⟩ := Option.map_eq_some_iff.mp h
  subst p
  rw [recoverWire_address]
  exact u.2


def groupWiring (e : RowEndpointSeating d) (even : Even L) (g : G) :
    J8SourceMoment.ColumnWiring (LocalRow d g) (LocalColumn d g) (LocalPort d (g := g)) :=
  wiringOfOption (localHit d e even)

/-- Distinct rows can now share a column vertex, but not the same physical port. -/
theorem no_repeated_shift_port (e : RowEndpointSeating d) (even : Even L)
    {g : G} (r s : LocalRow d g) (b c : Bool) (p : Sigma (LocalPort d (g := g)))
    (hr : localHit d e even r = some (b,p))
    (hs : localHit d e even s = some (c,p)) : r = s := by
  have h := localHit_sound d e even r hr
  have k := localHit_sound d e even s hs
  exact Subtype.ext (congrArg Prod.fst (predecessor_unique d h k))

#print axioms localHit_complete
#print axioms localHit_sound
#print axioms no_repeated_shift_port
end
end J8Physical.Relaxed
