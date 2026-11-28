import J6R11RepackSelect
import J6ActiveRun

/-! Every well-formed active host gets a selected real packing. The
certificate remembers the exact rounded maximum, not an enlarged padded
layout or an artificial second independent port allocation. -/
namespace J6R12Repack
open scoped Classical Polynomial
open P11FullPacking J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun
variable {f : ℤ[X]} {ell : ℕ}

/-- Packing witnesses depend on the graph of the current call, never on
an oracle for its contraction value. -/
structure Selected (H : PhysicalHost f ell) (a : ℕ) (G : Type)
    [LinearOrder G] [Fintype G] where
  packing : PhysicalPacking H.network a G
  minimal : packing.copies =
    ceilCopies (2^a) (maxFiber (declaredCell H.network packing.rowLabel packing.colLabel))

/-- The two printed inequalities which are needed for fresh packing;
the third, 2L ≤ Δ, is used for the degree of the next packet vertex. -/
structure PackingGuards (H : PhysicalHost f ell) (a Δ : ℕ) : Prop where
  degree : GoodDegree H Δ
  collision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ ≤ H.edgeCount
  slots : 2^a*J9PrintedSchedule.arrayCard a ≤ H.edgeCount

variable {G : Type} [LinearOrder G] [Fintype G]

noncomputable def fresh (H : PhysicalHost f ell) (a Δ : ℕ)
    (hG : Fintype.card G=64) (h : PackingGuards H a Δ) : Selected H a G :=
  let h' := host_can_repack H a Δ hG h.degree h.collision h.slots
  ⟨h'.choose,h'.choose_spec⟩

/-- Only meaningful call data can inherit the numeric bounds. This does
not assert a packing for arbitrary `Call` records with fake edge counts. -/
theorem guards_for_call (c : Call (PhysicalHost f ell)) (a Δ : ℕ)
    (validSize : c.host.edgeCount=c.edges) (degree : GoodDegree c.host Δ)
    (collision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ ≤ c.edges)
    (slots : 2^a*J9PrintedSchedule.arrayCard a ≤ c.edges) :
    PackingGuards c.host a Δ :=
  ⟨degree,validSize.symm ▸ collision,validSize.symm ▸ slots⟩

/-- Use the designated genuine root seating on the root itself. On every
other eligible call, select the fresh legal geometry using its own graph.
No proof of fresh numeric guards at the root is needed for this choice. -/
noncomputable def select (root : Call (PhysicalHost f ell)) (bits : ℕ → ℕ) (Δ : ℕ)
    (hG : Fintype.card G=64) (special : Selected root.host (bits root.depth) G)
    (c : Call (PhysicalHost f ell)) (h : c≠root → PackingGuards c.host (bits c.depth) Δ) :
    Selected c.host (bits c.depth) G :=
  if same : c=root then same.symm ▸ special else fresh c.host (bits c.depth) Δ hG (h same)

theorem select_root (root : Call (PhysicalHost f ell)) (bits : ℕ → ℕ) (Δ : ℕ)
    (hG : Fintype.card G=64) (special : Selected root.host (bits root.depth) G)
    (h : root≠root → PackingGuards root.host (bits root.depth) Δ) :
    select root bits Δ hG special root h = special := by
  simp [select]

theorem select_other (root : Call (PhysicalHost f ell)) (bits : ℕ → ℕ) (Δ : ℕ)
    (hG : Fintype.card G=64) (special : Selected root.host (bits root.depth) G)
    (c : Call (PhysicalHost f ell)) (h : c≠root → PackingGuards c.host (bits c.depth) Δ)
    (hother : c≠root) :
    select root bits Δ hG special c h = fresh c.host (bits c.depth) Δ hG (h hother) := by
  simp [select,hother]

/-- The exact packet bound from the chosen embedding. -/
theorem selected_packet_bound (H : PhysicalHost f ell) {a : ℕ} (s : Selected H a G) :
    Nat.card (Page a s.packing.copies G)*2^a ≤ 3*H.edgeCount := by
  rw [← host_card H]
  exact physical_packet_count s.packing

#print axioms fresh
#print axioms guards_for_call
#print axioms select_root
#print axioms select_other
#print axioms selected_packet_bound
end J6R12Repack
