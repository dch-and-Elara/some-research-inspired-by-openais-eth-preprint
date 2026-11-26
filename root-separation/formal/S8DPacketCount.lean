import S8DPacketSlots

namespace S8

open scoped BigOperators

variable {I A : Type*} [Fintype I] [DecidableEq I] [Fintype A]
  [LinearOrder A] [Nonempty A]

abbrev Unequal (p : PacketPattern I A) := {i : I // (p i).1.1 ≠ (p i).1.2}
abbrev Equal (p : PacketPattern I A) := {i : I // (p i).1.1 = (p i).1.2}

private def orientationBits (p : PacketPattern I A) (b : Unequal p → Bool) (i : I) : Bool :=
  if h : (p i).1.1 ≠ (p i).1.2 then b ⟨i,h⟩ else false

private theorem sorted_orientation (p : PacketPattern I A) (b : Unequal p → Bool)
    (i : Unequal p) :
    decide ((slotCell p (orientationBits p b)).2 i.1 < (slotCell p (orientationBits p b)).1 i.1) =
      b i := by
  have hn := i.2
  have hl := lt_of_le_of_ne (p i.1).2 hn
  cases hb : b i <;> simp [slotCell, orientationBits, hn, hl, hl.le, hb]

/-- Every ordered cell corresponds to exactly one unordered pattern and one
    choice of orientations on its unequal coordinates. -/
noncomputable def patternEquiv :
    (Σ p : PacketPattern I A, Unequal p → Bool) ≃ (I → A) × (I → A) :=
  Equiv.ofBijective (fun p => slotCell p.1 (orientationBits p.1 p.2)) (by
    constructor
    · intro x y h
      obtain ⟨p,b⟩ := x
      obtain ⟨q,c⟩ := y
      have hp := congrArg sortedPattern h
      simp only [slot_pattern] at hp
      subst q
      congr 1
      funext i
      exact (sorted_orientation p b i).symm.trans
        ((congrArg (fun z : (I → A) × (I → A) => decide (z.2 i.1 < z.1 i.1)) h).trans
          (sorted_orientation p c i))
    · intro cell
      let p := sortedPattern cell
      let b (i : Unequal p) := decide (cell.2 i.1 < cell.1 i.1)
      refine ⟨⟨p,b⟩,?_⟩
      calc
        _ = slotCell p (fun i => decide (cell.2 i < cell.1 i)) :=
          same_cell_of_unequal_bits _ _ _ (fun i hi => by simp [orientationBits, b, hi])
        _ = cell := cell_by_bits cell)

/-- Count the actual packet type of the slot injection. This charges exactly
    the volume of the common padded cell table. -/
theorem packet_volume (pad : ℕ) (divisible : 2 ^ Fintype.card I ∣ pad) :
    Fintype.card (Packet I A pad) * 2 ^ Fintype.card I =
      pad * Fintype.card ((I → A) × (I → A)) := by
  classical
  have hc := Fintype.card_congr (patternEquiv (I := I) (A := A))
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_bool] at hc
  rw [← hc]
  simp only [Packet, Fintype.card_sigma, Fintype.card_fin, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  have he : Fintype.card (Equal p) + Fintype.card (Unequal p) = Fintype.card I := by
    have h := Fintype.card_subtype_compl (fun i : I => (p i).1.1 = (p i).1.2)
    have hh := Fintype.card_subtype_le (fun i : I => (p i).1.1 = (p i).1.2)
    change Fintype.card (Unequal p) = Fintype.card I - Fintype.card (Equal p) at h
    change Fintype.card (Equal p) ≤ Fintype.card I at hh
    omega
  suffices (pad / 2 ^ Fintype.card (Equal p)) *
      ((2 ^ Fintype.card (Equal p)) * 2 ^ Fintype.card (Unequal p)) =
      pad * 2 ^ Fintype.card (Unequal p) by simpa only [← pow_add, he] using this
  rw [← Nat.mul_assoc, Nat.div_mul_cancel
    ((pow_dvd_pow 2 (Fintype.card_subtype_le (fun i : I => (p i).1.1 = (p i).1.2))).trans divisible)]

/-- The actual oriented source packets, with no wire collisions and the
    advertised 3M/L bound on the finite packet index type. -/
theorem certified_root_packets {W : Type*} [Fintype W]
    (cell : W → (I → A) × (I → A)) (Δ : ℚ) (cert : SourceDensity.CollisionCertificate cell Δ)
    (hSlots : 2 ^ Fintype.card I * Fintype.card ((I → A) × (I → A)) ≤ Fintype.card W) :
    let L := 2 ^ Fintype.card I
    let pad := paddedLoad cell L
    (∃ put : W ↪ Packet I A pad × (I → Bool),
      ∀ w, slotCell (put w).1.1 (put w).2 = cell w) ∧
    (Fintype.card (Packet I A pad) : ℚ) ≤ 3 * Fintype.card W / L := by
  classical
  intro L pad
  have hL : 0 < L := by dsimp only [L]; positivity
  have hdiv : L ∣ pad := by unfold pad paddedLoad; exact dvd_mul_left _ _
  refine ⟨embed_wires_into_packets cell pad hdiv (padded_load_max cell L hL), ?_⟩
  have hv := packet_volume (I := I) (A := A) pad hdiv
  change Fintype.card (Packet I A pad) * L =
    pad * Fintype.card ((I → A) × (I → A)) at hv
  have hv' : (Fintype.card (Packet I A pad) : ℚ) * L =
    (pad : ℚ) * Fintype.card ((I → A) × (I → A)) := by exact_mod_cast hv
  apply (le_div_iff₀ (by exact_mod_cast hL : (0 : ℚ) < L)).2
  rw [hv']
  exact (le_div_iff₀ (by positivity)).1 (padded_load_budget cell Δ cert L hL hSlots)

#print axioms certified_root_packets
#print axioms patternEquiv
#print axioms packet_volume

end S8

