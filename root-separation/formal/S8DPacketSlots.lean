import S8DPadding
import Mathlib.Logic.Equiv.Prod

namespace S8

variable {I A W : Type*} [Fintype I] [DecidableEq I] [Fintype A]
  [LinearOrder A] [Fintype W]

/-- One unordered-symbol pattern for a packet, represented by sorted endpoints. -/
abbrev PacketPattern (I A : Type*) [LE A] := I → {p : A × A // p.1 ≤ p.2}

def sortedPattern (cell : (I → A) × (I → A)) : PacketPattern I A :=
  fun i => ⟨(min (cell.1 i) (cell.2 i), max (cell.1 i) (cell.2 i)), min_le_max⟩

def slotCell (pattern : PacketPattern I A) (bits : I → Bool) : (I → A) × (I → A) :=
  (fun i => if bits i then (pattern i).1.2 else (pattern i).1.1,
   fun i => if bits i then (pattern i).1.1 else (pattern i).1.2)

omit [Fintype I] [DecidableEq I] [Fintype A] in
theorem slot_pattern (pattern : PacketPattern I A) (bits : I → Bool) :
    sortedPattern (slotCell pattern bits) = pattern := by
  funext i
  apply Subtype.ext
  change (min _ _, max _ _) = _
  have h := (pattern i).2
  cases hb : bits i <;> simp [slotCell, hb, min_eq_left h, max_eq_right h, min_eq_right h, max_eq_left h]

omit [Fintype I] [DecidableEq I] [Fintype A] in
theorem cell_by_bits (cell : (I → A) × (I → A)) :
    slotCell (sortedPattern cell) (fun i => decide (cell.2 i < cell.1 i)) = cell := by
  ext i
  all_goals
    by_cases h : cell.2 i < cell.1 i
    · simp [slotCell, sortedPattern, h, min_eq_right h.le, max_eq_left h.le]
    · have h' := le_of_not_gt h
      simp [slotCell, sortedPattern, h, min_eq_left h', max_eq_right h']

omit [Fintype I] [DecidableEq I] [Fintype A] in
theorem same_cell_of_unequal_bits (pattern : PacketPattern I A) (b c : I → Bool)
    (h : ∀ i, (pattern i).1.1 ≠ (pattern i).1.2 → b i = c i) :
    slotCell pattern b = slotCell pattern c := by
  ext i
  all_goals
    by_cases h' : (pattern i).1.1 = (pattern i).1.2
    · simp [slotCell, h']
    · simp [slotCell, h i h']

omit [Fintype A] in
/-- All padded occurrences of a cell fit in the allotted packets of its
    unordered pattern. Unequal positions fix the orientation bits and the
    equal positions give independent copy bits. Here rows indexed by W
    are actual occurrences of this one ordered cell. -/
theorem embed_cell_into_packet_slots (cell : (I → A) × (I → A)) (pad : ℕ)
    (divisible : 2 ^ Fintype.card I ∣ pad) (load : Fintype.card W ≤ pad) :
    let pattern := sortedPattern cell
    let equal := {i : I // (pattern i).1.1 = (pattern i).1.2}
    ∃ put : W ↪ Fin (pad / 2 ^ Fintype.card equal) × (I → Bool),
      ∀ w, slotCell pattern (put w).2 = cell := by
  classical
  intro pattern Equal
  let Q := 2 ^ Fintype.card Equal
  have hdiv : Q ∣ pad :=
    (pow_dvd_pow 2 (Fintype.card_subtype_le _)).trans divisible
  have hsize : Fintype.card (Fin (pad / Q) × (Equal → Bool)) = pad := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, Fintype.card_bool]
    exact Nat.div_mul_cancel hdiv
  let index : W ↪ Fin (pad / Q) × (Equal → Bool) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by rw [hsize]; exact load))
  let bits (b : Equal → Bool) (i : I) : Bool :=
    if h : (pattern i).1.1 = (pattern i).1.2 then b ⟨i,h⟩ else decide (cell.2 i < cell.1 i)
  have hinj : Function.Injective bits := by
    intro b c h
    funext x
    simpa [bits, x.2] using congrFun h x.1
  refine ⟨⟨fun w => ((index w).1, bits (index w).2), ?_⟩, fun w => ?_⟩
  · intro v w eq
    change ((index v).1, bits (index v).2) = ((index w).1, bits (index w).2) at eq
    obtain ⟨h₁,h₂⟩ := Prod.mk.inj eq
    exact index.injective (Prod.ext h₁ (hinj h₂))
  · change slotCell pattern (bits (index w).2) = cell
    calc
      _ = slotCell pattern (fun i => decide (cell.2 i < cell.1 i)) :=
        same_cell_of_unequal_bits _ _ _ (fun i hi => by simp [bits, hi])
      _ = cell := cell_by_bits cell

abbrev Packet (I A : Type*) [LE A] [DecidableEq A] [Fintype I] (pad : ℕ) :=
  Σ pattern : PacketPattern I A, Fin (pad / 2 ^ Fintype.card {i : I // (pattern i).1.1 = (pattern i).1.2})

omit [Fintype A] in
/-- A global injection of physical wires into source packet slots. Reading two
    different cells from a common slot is impossible, so per-cell packing glues
    without any conflicts between ordered cell classes. -/
theorem embed_wires_into_packets (cells : W → (I → A) × (I → A)) (pad : ℕ)
    (divisible : 2 ^ Fintype.card I ∣ pad)
    (load : ∀ c, SourceDensity.fiberCount cells c ≤ pad) :
    ∃ put : W ↪ Packet I A pad × (I → Bool),
      ∀ w, slotCell (put w).1.1 (put w).2 = cells w := by
  classical
  have existsPut (c : (I → A) × (I → A)) := embed_cell_into_packet_slots
    (W := {w : W // cells w = c}) c pad divisible (by
      simpa [SourceDensity.fiberCount, Fintype.card_subtype] using load c)
  choose put correct using existsPut
  let place (w : W) : Packet I A pad × (I → Bool) :=
    let z := put (cells w) ⟨w,rfl⟩
    (⟨sortedPattern (cells w), z.1⟩, z.2)
  have hcorrect (w : W) : slotCell (place w).1.1 (place w).2 = cells w :=
    correct (cells w) ⟨w,rfl⟩
  refine ⟨⟨place, ?_⟩, hcorrect⟩
  intro w v equal
  have sameCell : cells w = cells v := by rw [← hcorrect w, ← hcorrect v, equal]
  let encode (c : (I → A) × (I → A)) (w : {w : W // cells w = c}) :
      Packet I A pad × (I → Bool) :=
    (⟨sortedPattern c, (put c w).1⟩, (put c w).2)
  have samePlace : encode (cells w) ⟨w,rfl⟩ = encode (cells w) ⟨v,sameCell.symm⟩ := by
    have hv (c : (I → A) × (I → A)) (hc : cells v = c) :
        place v = encode c ⟨v,hc⟩ := by subst c; rfl
    exact equal.trans (hv _ sameCell.symm)
  have h₁ := Sigma.mk.inj (congrArg (fun z : Packet I A pad × (I → Bool) => z.1) samePlace)
  have h₂ := congrArg (fun z : Packet I A pad × (I → Bool) => z.2) samePlace
  have result := (put (cells w)).injective (Prod.ext (eq_of_heq h₁.2) h₂)
  exact congrArg Subtype.val result

#print axioms embed_wires_into_packets
#print axioms slot_pattern
#print axioms cell_by_bits
#print axioms embed_cell_into_packet_slots

end S8



