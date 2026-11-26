import RootEntry
import S8DPacketCount
import S8DeterministicPlacement

/-! Appendix D 114–171: complete-label collision and actual ordered slots.
The greedy score is the source's sum of pair agreement probabilities,
scaled to integers using at most four vertex labels per test. -/

namespace RootSeparation

open SourceDensity ProductVariance
open scoped BigOperators
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

section Collision

variable {W X Y A : Type*} [Fintype W] [DecidableEq W]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype A] [DecidableEq A] [Nonempty A]

def site (row : W → X) (col : W → Y) (w : W) : Bool → X ⊕ Y
  | false => .inl (row w)
  | true => .inr (col w)

noncomputable def labelOrder : List (X ⊕ Y) := Finset.univ.toList
noncomputable def labelChoices : List A := Finset.univ.toList

noncomputable def selectedLabels (row : W → X) (col : W → Y) (zero : A) : X ⊕ Y → A :=
  S8.Prefix.collisionSolve (site row col) labelOrder labelChoices zero

def cellAt (row : W → X) (col : W → Y) (label : X ⊕ Y → A) (w : W) : A × A :=
  (label (.inl (row w)), label (.inr (col w)))

private def boolPair : (Bool → A) ≃ A × A where
  toFun f := (f false, f true)
  invFun p b := if b then p.2 else p.1
  left_inv f := by funext b; cases b <;> rfl
  right_inv p := rfl

private theorem collision_cellAt (row : W → X) (col : W → Y)
    (label : X ⊕ Y → A) :
    S8.collision (cellAt row col label) = S8.collision (fun w => label ∘ site row col w) := by
  rw [S8.collision_pair, S8.collision_pair, Fintype.card_congr (boolPair (A := A))]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro f _
  change (if boolPair (label ∘ site row col e) = boolPair (label ∘ site row col f)
    then (1 : ℚ) else 0) = _
  simp only [Equiv.apply_eq_iff_eq]

private def sharedPairs (row : W → X) (col : W → Y) : Finset (W × W) :=
  Finset.univ.filter fun p => row p.1 = row p.2 ∨ col p.1 = col p.2

private theorem unshared (row : W → X) (col : W → Y)
    (e f : W) (h : (e,f) ∉ sharedPairs row col) :
    Function.Injective (Sum.elim (site row col e) (site row col f)) := by
  have hne : row e ≠ row f ∧ col e ≠ col f := by simpa [sharedPairs] using h
  rintro (b | b) (c | c) hbc <;> cases b <;> cases c <;> simp_all [site]

private theorem sharedPairs_card (row : W → X) (col : W → Y) (Δ : ℕ)
    (hr : ∀ v, fiberCount row v ≤ Δ) (hc : ∀ v, fiberCount col v ≤ Δ) :
    (sharedPairs row col).card ≤ 2 * Fintype.card W * Δ := by
  classical
  have he : (sharedPairs row col).card =
      ∑ e : W, (Finset.univ.filter fun f => row e = row f ∨ col e = col f).card := by
    simp only [sharedPairs, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  rw [he]
  calc
    _ ≤ ∑ _e : W, (2 * Δ) := by
      apply Finset.sum_le_sum
      intro e _
      let R := Finset.univ.filter (fun f => row f = row e)
      let C := Finset.univ.filter (fun f => col f = col e)
      have h : (Finset.univ.filter fun f => row e = row f ∨ col e = col f) = R ∪ C := by
        ext f
        simp [R, C, eq_comm]
      rw [h]
      exact (Finset.card_union_le _ _).trans (by
        have h1 := hr (row e)
        have h2 := hc (col e)
        change R.card ≤ Δ at h1
        change C.card ≤ Δ at h2
        omega)
    _ = _ := by simp; ring

theorem selected_collision (row : W → X) (col : W → Y) (zero : A) (Δ : ℕ)
    (hr : ∀ v, fiberCount row v ≤ Δ) (hc : ∀ v, fiberCount col v ≤ Δ) :
    S8.collision (cellAt row col (selectedLabels row col zero)) ≤
      2 * (Fintype.card W : ℚ) * Δ := by
  classical
  rw [collision_cellAt]
  have havg := S8.primitive_collision_bound (A := A) (site row col) (sharedPairs row col)
    (unshared row col)
  have havg' : uniformMean (fun ω : X ⊕ Y → A => S8.collision (fun w => ω ∘ site row col w)) ≤
      (sharedPairs row col).card := by simpa only [uniformMean, Finset.mul_sum] using havg
  have hsolve := S8.Prefix.collisionSolve_le (site row col) labelOrder
    (Finset.nodup_toList _) (by simp [labelOrder]) labelChoices (by simp [labelChoices]) zero
  exact hsolve.trans (havg'.trans (by exact_mod_cast sharedPairs_card row col Δ hr hc))

end Collision

section Packet

variable {W : Type*} [Fintype W]

private def slotNumber {a : ℕ} (bits : Fin a → Bool) : Fin (2^a) :=
  Fin.cast (congrArg (fun k : ℕ => 2^k) (List.length_ofFn (f := bits)))
    (BitVec.ofBoolListLE (List.ofFn bits)).toFin

private theorem slotNumber_bit {a : ℕ} (bits : Fin a → Bool) (i : Fin a) :
    (slotNumber bits).val.testBit i.val = bits i := by
  change (BitVec.ofBoolListLE (List.ofFn bits)).toNat.testBit i.val = bits i
  rw [BitVec.testBit_toNat, BitVec.getLsbD_ofBoolListLE]
  simp

private theorem slotNumber_injective {a : ℕ} :
    Function.Injective (@slotNumber a) := by
  intro x y h
  funext i
  rw [← slotNumber_bit x i, ← slotNumber_bit y i, h]

abbrev RootCell (a : ℕ) := (Fin a → Fin 64) × (Fin a → Fin 64)

def exactPad {a : ℕ} (cell : W → RootCell a) : ℕ :=
  let L := 2^a
  S11.ceilDiv (Finset.univ.sup (fiberCount cell)) L * L

/-- Round the maximum cell load up to a multiple of L, as in 149–166. -/
theorem exact_packets {a : ℕ} (cell : W → RootCell a) (Δ : ℚ)
    (cert : CollisionCertificate cell Δ)
    (hSlots : 2^a * Fintype.card (RootCell a) ≤ Fintype.card W) :
    ∃ G : S11.Packing W (S8.Packet (Fin a) (Fin 64) (exactPad cell)) a (2^a),
      G.cell = cell ∧
      Fintype.card (S8.Packet (Fin a) (Fin 64) (exactPad cell)) * 2^a ≤ 3 * Fintype.card W := by
  classical
  let L := 2^a
  let pad := exactPad cell
  have hL : 0 < L := by dsimp [L]; positivity
  have hdiv : 2 ^ Fintype.card (Fin a) ∣ pad := by
    simpa [pad, exactPad] using (dvd_mul_left L
      (S11.ceilDiv (Finset.univ.sup (fiberCount cell)) L))
  have hload (c : RootCell a) : fiberCount cell c ≤ pad := by
    have h := Finset.le_sup (f := fiberCount cell) (s := Finset.univ) (Finset.mem_univ c)
    have hm := Nat.mod_add_div (Finset.univ.sup (fiberCount cell) + L - 1) L
    have hl := Nat.mod_lt (Finset.univ.sup (fiberCount cell) + L - 1) hL
    change fiberCount cell c ≤ ((Finset.univ.sup (fiberCount cell) + L - 1) / L) * L
    rw [Nat.mul_comm]
    omega
  obtain ⟨put, hp⟩ := S8.embed_wires_into_packets cell pad hdiv hload
  let bmap : (Fin a → Bool) ↪ Fin (2^a) := ⟨slotNumber, slotNumber_injective⟩
  let G : S11.Packing W (S8.Packet (Fin a) (Fin 64) pad) a L :=
    { position := put.trans ((Function.Embedding.refl _).prodMap bmap)
      cell := cell
      pair := fun p i => (p.1 i).val
      orientation := by
        intro w i
        change ( (cell w).1 i, (cell w).2 i) =
          if (slotNumber (put w).2).val.testBit i.val then ((put w).1.1 i).val.swap
          else ((put w).1.1 i).val
        rw [slotNumber_bit, ← hp w]
        cases h : (put w).2 i <;> simp [S8.slotCell, h, Prod.swap] }
  refine ⟨G, rfl, ?_⟩
  have hvolume := S8.packet_volume (I := Fin a) (A := Fin 64) pad hdiv
  rw [Fintype.card_fin] at hvolume
  rw [hvolume]
  have hp' : pad ≤ S8.paddedLoad cell L := by
    have hn := Nat.div_le_div_right (c := L) (show Finset.univ.sup (fiberCount cell) + L - 1
        ≤ Finset.univ.sup (fiberCount cell) + L by omega)
    rw [Nat.add_div_right _ hL] at hn
    exact Nat.mul_le_mul_right L hn
  have hb := S8.padded_load_budget cell Δ cert L hL hSlots
  have hcast : (pad : ℚ) ≤ S8.paddedLoad cell L := by exact_mod_cast hp'
  have hbound := (le_div_iff₀ (by positivity : (0 : ℚ) < Fintype.card (RootCell a))).mp
    (hcast.trans hb)
  exact_mod_cast hbound

/-- The real-port quota on either side, Appendix D 126–127. The actual
full-cell collision bound gives the stronger 2M/r quota. -/
theorem packet_group_quota {a : ℕ} (cell : W → RootCell a) (Δ : ℚ)
    (cert : CollisionCertificate cell Δ) (j : Fin a) (b : Bool) (g : Fin 64) :
    (fiberCount (fun w => (if b then (cell w).2 else (cell w).1) j) g : ℚ) ≤
      3 * Fintype.card W / 64 := by
  let proj (c : RootCell a) := (if b then c.2 else c.1) j
  let k := Fintype.card (Fin 64) ^ (Fintype.card (Fin a)-1) *
    Fintype.card (Fin 64) ^ Fintype.card (Fin a)
  have hk (x : Fin 64) : fiberCount proj x = k := by
    cases b
    · exact BalancedUnion.single_coordinate_fiber j x
    · exact MainIncidence.factor_symbol_fiber j x
  have h := projected_port_bound cell Δ cert proj k hk g
  rw [Fintype.card_fin, Nat.cast_ofNat] at h
  have hM : (0 : ℚ) ≤ Fintype.card W := by positivity
  change (fiberCount (fun w => proj (cell w)) g : ℚ) ≤ _
  linarith

end Packet

#print axioms selected_collision
#print axioms exact_packets
#print axioms packet_group_quota
end RootSeparation
