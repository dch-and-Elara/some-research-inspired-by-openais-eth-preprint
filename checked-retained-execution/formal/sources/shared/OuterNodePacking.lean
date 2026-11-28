import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace OuterNodePacking

abbrev Slot (P : Type*) (L : ℕ) := P × Fin L

/-- Columns reached by a real row in the same physical packet after integer shift t.
Both endpoints are required to be real; no wrap around is permitted. -/
def matchedColumns {P : Type*} [DecidableEq P] {L : ℕ}
    (packets : Finset P) (rowReal colReal : Slot P L → Bool) (t : ℤ) :
    Finset (Slot P L) :=
  (packets.product Finset.univ).filter fun y =>
    colReal y = true ∧
      ∃ x : Fin L, rowReal (y.1, x) = true ∧ (x.val : ℤ) + t = (y.2.val : ℤ)

/-- The corresponding set of matched row ports. -/
def matchedRows {P : Type*} [DecidableEq P] {L : ℕ}
    (packets : Finset P) (rowReal colReal : Slot P L → Bool) (t : ℤ) :
    Finset (Slot P L) :=
  (packets.product Finset.univ).filter fun x =>
    rowReal x = true ∧
      ∃ y : Fin L, colReal (x.1, y) = true ∧ (x.2.val : ℤ) + t = (y.val : ℤ)

theorem mem_matchedColumns {P : Type*} [DecidableEq P] {L : ℕ}
    (packets : Finset P) (rowReal colReal : Slot P L → Bool) (t : ℤ)
    (y : Slot P L) :
    y ∈ matchedColumns packets rowReal colReal t ↔
      y.1 ∈ packets ∧ colReal y = true ∧
      ∃ x : Fin L, rowReal (y.1, x) = true ∧ (x.val : ℤ) + t = (y.2.val : ℤ) := by
  simp [matchedColumns]

theorem mem_matchedRows {P : Type*} [DecidableEq P] {L : ℕ}
    (packets : Finset P) (rowReal colReal : Slot P L → Bool) (t : ℤ)
    (x : Slot P L) :
    x ∈ matchedRows packets rowReal colReal t ↔
      x.1 ∈ packets ∧ rowReal x = true ∧
      ∃ y : Fin L, colReal (x.1, y) = true ∧ (x.2.val : ℤ) + t = (y.val : ℤ) := by
  simp [matchedRows]

/-- The outer shift has only one geometrically possible pair of slots.
Both assertions still apply when only one of the two slots is real. -/
theorem outer_pair_is_boundary {L : ℕ} (x y : Fin L)
    (h : (x.val : ℤ) + ((L : ℤ) - 1) = (y.val : ℤ)) :
    x.val = 0 ∧ y.val = L - 1 := by
  have hx := x.isLt
  have hy := y.isLt
  omega

theorem outer_matchedColumn_at_right {P : Type*} [DecidableEq P] {L : ℕ}
    (packets : Finset P) (rowReal colReal : Slot P L → Bool)
    {y : Slot P L}
    (hy : y ∈ matchedColumns packets rowReal colReal ((L : ℤ) - 1)) :
    y.2.val = L - 1 := by
  obtain ⟨_, _, x, _, h⟩ := (mem_matchedColumns packets rowReal colReal _ y).1 hy
  exact (outer_pair_is_boundary x y.2 h).2

theorem outer_matchedRow_at_left {P : Type*} [DecidableEq P] {L : ℕ}
    (packets : Finset P) (rowReal colReal : Slot P L → Bool)
    {x : Slot P L}
    (hx : x ∈ matchedRows packets rowReal colReal ((L : ℤ) - 1)) :
    x.2.val = 0 := by
  obtain ⟨_, _, y, _, h⟩ := (mem_matchedRows packets rowReal colReal _ x).1 hx
  exact (outer_pair_is_boundary x.2 y h).1

/-- There is at most one actual shifted column port per packet at t=L-1. -/
theorem outer_matched_card_le_packets {P : Type*} [DecidableEq P] {L : ℕ}
    (packets : Finset P) (rowReal colReal : Slot P L → Bool) :
    (matchedColumns packets rowReal colReal ((L : ℤ) - 1)).card ≤ packets.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro y hy
    exact ((mem_matchedColumns packets rowReal colReal _ y).1 hy).1
  · intro y hy z hz h
    apply Prod.ext h
    apply Fin.ext
    rw [outer_matchedColumn_at_right packets rowReal colReal hy,
      outer_matchedColumn_at_right packets rowReal colReal hz]

/-- Old equality vertices hit by at least one actual real shifted column port. -/
def touched {A V : Type*} [DecidableEq V] (old : Finset V)
    (owner : A → V) (matched : Finset A) : Finset V :=
  old ∩ matched.image owner

/-- Untouched vertices use none of the matched original column ports. -/
def untouched {A V : Type*} [DecidableEq V] (old : Finset V)
    (owner : A → V) (matched : Finset A) : Finset V :=
  old \ matched.image owner

theorem touched_le_ports {A V : Type*} [DecidableEq V] (old : Finset V)
    (owner : A → V) (matched : Finset A) :
    (touched old owner matched).card ≤ matched.card := by
  exact (Finset.card_le_card (fun _ h => (Finset.mem_inter.mp h).2)).trans
    Finset.card_image_le

theorem untouched_no_matched_port {A V : Type*} [DecidableEq V] (old : Finset V)
    (owner : A → V) (matched : Finset A) {v : V}
    (hv : v ∈ untouched old owner matched) :
    ∀ p ∈ matched, owner p ≠ v := by
  intro p hp h
  exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_image.mpr ⟨p, hp, h⟩)

theorem untouched_add_ports {A V : Type*} [DecidableEq V] (old : Finset V)
    (owner : A → V) (matched : Finset A) :
    old.card ≤ (untouched old owner matched).card + matched.card := by
  have hEq := Finset.card_sdiff_add_card_inter old (matched.image owner)
  have hLt := touched_le_ports old owner matched
  change (untouched old owner matched).card + (touched old owner matched).card = old.card
    at hEq
  omega

/-- Finite J9 count on every certified layout, without assumptions on how
the real ports within a packet were ordered. The RHS is in rationals, so
there is no silently rounded use of M/6 or 3 M/L. -/
theorem j9_untouched_lower {P V : Type*} [DecidableEq P] [DecidableEq V] {L : ℕ}
    (packets : Finset P) (rowReal colReal : Slot P L → Bool)
    (oldEq : Finset V) (owner : Slot P L → V) (M : ℕ)
    (hL : 0 < L) (hEq : M ≤ 6 * oldEq.card) (hPack : packets.card * L ≤ 3 * M) :
    (M : ℚ) / 6 - 3 * (M : ℚ) / L ≤
      ((untouched oldEq owner
        (matchedColumns packets rowReal colReal ((L : ℤ) - 1))).card : ℚ) := by
  let cols := matchedColumns packets rowReal colReal ((L : ℤ) - 1)
  have hGeom : cols.card ≤ packets.card := outer_matched_card_le_packets
    packets rowReal colReal
  have hNat := (untouched_add_ports oldEq owner cols).trans (Nat.add_le_add_left hGeom _)
  have hOld : ((oldEq.card : ℕ) : ℚ) ≤
      ((untouched oldEq owner cols).card : ℚ) + (packets.card : ℚ) := by
    exact_mod_cast hNat
  have hEq' : (M : ℚ) ≤ 6 * (oldEq.card : ℚ) := by exact_mod_cast hEq
  have hPack' : (packets.card : ℚ) * (L : ℚ) ≤ 3 * (M : ℚ) := by
    exact_mod_cast hPack
  have hL' : 0 < (L : ℚ) := by exact_mod_cast hL
  have hP : (packets.card : ℚ) ≤ 3 * (M : ℚ) / L := (le_div_iff₀ hL').2 hPack'
  change (M : ℚ) / 6 - 3 * (M : ℚ) / L ≤ ((untouched oldEq owner cols).card : ℚ)
  linarith

/-- The four-clone numerical specialization of J9: exactly 4N trivalent
old equality columns and 24N physical wires are inputs to this theorem. -/
theorem j9_four_clone {P V : Type*} [DecidableEq P] [DecidableEq V] {L : ℕ}
    (packets : Finset P) (rowReal colReal : Slot P L → Bool)
    (oldEq : Finset V) (owner : Slot P L → V) (N : ℕ)
    (hL : 0 < L) (hEq : oldEq.card = 4 * N)
    (hPack : packets.card * L ≤ 3 * (24 * N)) :
    (24 * (N : ℚ)) / 6 - 3 * (24 * (N : ℚ)) / L ≤
      ((untouched oldEq owner
        (matchedColumns packets rowReal colReal ((L : ℤ) - 1))).card : ℚ) := by
  have hM : 24 * N ≤ 6 * oldEq.card := by omega
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    j9_untouched_lower packets rowReal colReal oldEq owner (24 * N) hL hM hPack

/-- Assigning one bit to each untouched equality assigns that bit at every
port owned by that equality; all other ports are held at zero. -/
def equalityBits {A V : Type*} [DecidableEq V] (ports : Finset A) (keep : Finset V)
    (owner : A → V) (b : {v // v ∈ keep} → Bool) :
    {p // p ∈ ports} → Bool :=
  fun p => if hv : owner p.val ∈ keep then b ⟨owner p.val, hv⟩ else false

/-- If every selected equality owns a real port, its free equality bit can be
read back at such a port. Thus the untouched vertices really give independent
choices, not a count of ports duplicating the same equality bit. -/
theorem equalityBits_injective {A V : Type*} [DecidableEq V]
    (ports : Finset A) (keep : Finset V) (owner : A → V)
    (hOwners : ∀ v ∈ keep, ∃ p ∈ ports, owner p = v) :
    Function.Injective (equalityBits ports keep owner) := by
  intro f g h
  funext v
  obtain ⟨p, hp, howner⟩ := hOwners v.val v.property
  have hh := congrFun h (⟨p, hp⟩ : {p // p ∈ ports})
  simpa [equalityBits, howner, v.property] using hh

/-- J7 geometric interface. Physical slots have fixed wire IDs, distinct
on real slots; their endpoint seats come from a nonpin wire matching.
At the outer center the reached rows and columns are therefore partial
matchings on the original vertex owners, and no original pin is reached. -/
theorem j7_nonpin_endpoint_matching
    {P W U V : Type*} [DecidableEq P] [DecidableEq V] {L : ℕ}
    (packets : Finset P) (real : Slot P L → Bool) (wire : Slot P L → W)
    (rowOwner : W → U) (colOwner : W → V) (matching : Set W) (pins : Finset V)
    (hWire : Set.InjOn wire {p | real p = true})
    (hFill : ∀ p : Slot P L, p.1 ∈ packets → real p = true →
      (p.2.val = 0 ∨ p.2.val = L - 1) → wire p ∈ matching)
    (hRow : matching.InjOn rowOwner) (hCol : matching.InjOn colOwner)
    (hPins : ∀ e ∈ matching, colOwner e ∉ pins) :
    Set.InjOn (rowOwner ∘ wire)
      ↑(matchedRows packets real real ((L : ℤ) - 1)) ∧
    Set.InjOn (colOwner ∘ wire)
      ↑(matchedColumns packets real real ((L : ℤ) - 1)) ∧
    (∀ p ∈ matchedColumns packets real real ((L : ℤ) - 1),
      colOwner (wire p) ∉ pins) := by
  have hR : ∀ p ∈ matchedRows packets real real ((L : ℤ) - 1),
      real p = true ∧ wire p ∈ matching := by
    intro p hp
    obtain ⟨hP, hv, _⟩ := (mem_matchedRows packets real real _ p).1 hp
    exact ⟨hv, hFill p hP hv (Or.inl (outer_matchedRow_at_left packets real real hp))⟩
  have hC : ∀ p ∈ matchedColumns packets real real ((L : ℤ) - 1),
      real p = true ∧ wire p ∈ matching := by
    intro p hp
    obtain ⟨hP, hv, _⟩ := (mem_matchedColumns packets real real _ p).1 hp
    exact ⟨hv, hFill p hP hv (Or.inr (outer_matchedColumn_at_right packets real real hp))⟩
  refine ⟨?_, ?_, fun p hp => hPins (wire p) (hC p hp).2⟩
  · intro p hp q hq h
    exact hWire (hR p hp).1 (hR q hq).1
      (hRow (hR p hp).2 (hR q hq).2 h)
  · intro p hp q hq h
    exact hWire (hC p hp).1 (hC q hq).1
      (hCol (hC p hp).2 (hC q hq).2 h)


/-- If a chosen layout really seats both endpoints of every packet, the
outer partial shift has one real matched column per packet, not merely at most one. -/
theorem outer_matched_card_eq_of_full_endpoints {P : Type*} [DecidableEq P] {L : ℕ}
    (packets : Finset P) (rowReal colReal : Slot P L → Bool) (hL : 0 < L)
    (hRow : ∀ p ∈ packets, rowReal (p, ⟨0, hL⟩) = true)
    (hCol : ∀ p ∈ packets, colReal (p, ⟨L - 1, by omega⟩) = true) :
    (matchedColumns packets rowReal colReal ((L : ℤ) - 1)).card = packets.card := by
  apply le_antisymm (outer_matched_card_le_packets packets rowReal colReal)
  apply Finset.card_le_card_of_injOn (fun p => (p, (⟨L - 1, by omega⟩ : Fin L)))
  · intro p hp
    apply (mem_matchedColumns packets rowReal colReal _ _).2
    refine ⟨hp, hCol p hp, ⟨0, hL⟩, hRow p hp, ?_⟩
    change (0 : ℤ) + ((L : ℤ) - 1) = ((L - 1 : ℕ) : ℤ)
    omega
  · intro p hp q hq he
    exact congrArg Prod.fst he

/-- A free bit on an untouched owner never changes a shifted column port. -/
theorem equalityBits_zero_on_matched {A V : Type*} [DecidableEq V]
    (ports matched : Finset A) (hports : matched ⊆ ports)
    (old : Finset V) (owner : A → V)
    (b : {v // v ∈ untouched old owner matched} → Bool) :
    ∀ p (hp : p ∈ matched),
      equalityBits ports (untouched old owner matched) owner b ⟨p, hports hp⟩ = false := by
  intro p hp
  unfold equalityBits
  apply dif_neg
  intro h
  exact untouched_no_matched_port old owner matched h p hp rfl

/-- Reformulation of the owner injectivity in J7 as a literal bound of one
on the number of shifted ports of each original vertex. -/
theorem matched_vertex_at_most_one {A V : Type*} [DecidableEq V] (s : Finset A)
    (owner : A → V) (h : Set.InjOn owner ↑s) (v : V) :
    (s.filter fun p => owner p = v).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  obtain ⟨hpS, hpV⟩ := Finset.mem_filter.mp hp
  obtain ⟨hqS, hqV⟩ := Finset.mem_filter.mp hq
  exact h hpS hqS (hpV.trans hqV.symm)

#print axioms outer_matched_card_eq_of_full_endpoints
#print axioms equalityBits_zero_on_matched
#print axioms matched_vertex_at_most_one
#print axioms outer_pair_is_boundary
#print axioms outer_matched_card_le_packets
#print axioms touched_le_ports
#print axioms untouched_no_matched_port
#print axioms j9_untouched_lower
#print axioms j9_four_clone
#print axioms equalityBits_injective
#print axioms j7_nonpin_endpoint_matching

end OuterNodePacking
