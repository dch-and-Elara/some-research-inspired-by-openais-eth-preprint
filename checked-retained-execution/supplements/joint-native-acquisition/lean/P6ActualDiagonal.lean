import P6ScopePrimitive
import J7SeatRounded

open scoped Polynomial BigOperators Classical
open P11FullPacking P1DyadicGrid NativeProbeRing
namespace P6Joint
noncomputable section

variable {K E : Type*} [Fintype E] [LinearOrder K] {a b : ℕ}

def diagCell (word : Fin a → K) : Cell (Fin a) K := fun i => (word i,word i)

theorem diag_hot_empty (word : Fin a → K) : IsEmpty (Hot (key (diagCell word))) := by
  refine ⟨?_⟩
  intro x
  exact x.2 (by simp [diagCell,key,sortPair])

theorem diagonal_packet_card (word : Fin a → K) :
    Fintype.card (Packet b (key (diagCell word))) = b := by
  letI := diag_hot_empty word
  rw [← Nat.card_eq_fintype_card,packet_card]
  simp

theorem diagonal_cell_uniform (word : Fin a → K) (mask : MaskFamily a b K)
    (page : Packet b (key (diagCell word))) (slot : Fin (2^a)) :
    physicalCell mask (⟨key (diagCell word),page⟩,slot) = diagCell word := by
  funext i
  simp [physicalCell,diagCell,cell,key,sortPair]

/-- Occupancy in an actual diaphragm of the physical seat chart, not a
virtual padded packet. Without a lower cell occupancy only two endpoints
per page follow from the published matching certificate. -/
theorem exists_dense_actual_diagonal_page
    (mask : MaskFamily a b K) (seat : E ↪ Physical a b K)
    (word : Fin a → K) (hb : 0<b) (r : ℕ)
    (enough : b*r ≤ (Finset.univ.filter (fun e => physicalCell mask (seat e) = diagCell word)).card) :
    ∃ packet : Packet b (key (diagCell word)),
      r ≤ (Finset.univ.filter (fun e : E =>
        (seat e).1 = ⟨key (diagCell word),packet⟩)).card := by
  classical
  let q := (Finset.univ : Finset E).filter (fun e => physicalCell mask (seat e) = diagCell word)
  let t := ((Finset.univ : Finset (Packet b (key (diagCell word)))).map
    ⟨fun packet => (⟨key (diagCell word),packet⟩ : Page a b K), fun _ _ h => eq_of_heq (Sigma.mk.inj_iff.mp h).2⟩)
  have hMap : q.toSet.MapsTo (fun e => (seat e).1) t := by
    intro e he
    have hCell := (Finset.mem_filter.mp he).2
    have hk : (seat e).1.1 = key (diagCell word) := by
      have H := congrArg key hCell
      simpa [physicalCell,key_cell] using H
    rcases hSeat : (seat e).1 with ⟨k,p⟩
    rw [hSeat] at hk
    dsimp only at hk
    subst k
    exact Finset.mem_map.mpr ⟨p,Finset.mem_univ _,hSeat.symm⟩
  have ht : t.card=b := by
    simp only [t,Finset.card_map,Finset.card_univ,diagonal_packet_card]
  by_contra! fail
  have hne : t.Nonempty := Finset.card_pos.mp (by rw [ht]; exact hb)
  have hSum : q.card < ∑ _ ∈ t, r := by
    rw [Finset.card_eq_sum_card_fiberwise hMap]
    apply Finset.sum_lt_sum_of_nonempty hne
    intro pg hg
    obtain ⟨pkt,_,rfl⟩ := Finset.mem_map.mp hg
    refine lt_of_le_of_lt (Finset.card_le_card ?_) (fail pkt)
    · intro e he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp he).2⟩
  have hTotal : (∑ _ ∈ t, r) = b*r := by simp [ht]
  change b*r ≤ q.card at enough
  omega

/-- Both sides of the published cell-deviation estimates matter.
Let μ be its exact uniform center, E the certified deviation and L the
actual packet length. The padding bound bL≤μ+E+L (maximum plus rounding)
and μ≥3E+L imply at least half the real cell's padded capacity. -/
theorem dense_of_rounded_deviation {a b load r : ℕ} (mu e : ℚ)
    (he : 0 ≤ e)
    (hdev : ((load:ℚ)-mu)^2 ≤ e^2)
    (hp : (b:ℚ)*(2:ℚ)^a ≤ mu+e+(2:ℚ)^a)
    (hbig : 3*e+(2:ℚ)^a ≤ mu)
    (hr : 2*r ≤ 2^a) :
    b*r ≤ load := by
  have hl := J7SeatQuota.deviation_lower (load:ℚ) mu e he hdev
  have hr' : 2*(r:ℚ) ≤ (2:ℚ)^a := by exact_mod_cast hr
  have hmul := mul_le_mul_of_nonneg_left hr' (by positivity : 0 ≤ (b:ℚ))
  have hcalc : (b:ℚ)*(r:ℚ) ≤ load := by nlinarith
  exact_mod_cast hcalc

section SourceOccupancy
open J7SeatPacking J7SeatSource J7FullWordCells J7FullWordAssembly J7SourceLabels J7SourceConditioning
variable {A Pair Row Col W : Type*} [LinearOrder A] [Fintype A]
  [Fintype Pair] [Fintype W] {a0 b0 : ℕ}

/-- Connect source load deviation and rounded packing to the actual
fiber of the seat embedding. The asymptotic region is represented by
the explicit inequality 3E+L≤μ, not silently assumed for small sizes. -/
theorem diagonal_load_from_source_variance (row : W → Row)
    (col : W → OrdinaryColumn Pair Col)
    (z : State A (Fin a0 → A) Pair Row Col)
    (seat : Wire Pair W ↪ Physical (a0+1) b0 A)
    (seat_eq : ∀ w, physicalCell (balancedMask (a0+1) b0) (seat w) = wordLabel row col z w)
    (word : Fin (a0+1) → A) (dev : ℚ) (he : 0≤dev)
    (hdev : ∀ c, ((∑ w : Wire Pair W, indicator (fullCell row col w z) c) -
      (Fintype.card (Wire Pair W) : ℚ) / denom A (Fin a0 → A))^2 ≤ dev^2)
    (hp : (b0:ℚ)*2^(a0+1) ≤ (Fintype.card (Wire Pair W) : ℚ) / denom A (Fin a0 → A) + dev + 2^(a0+1))
    (hbig : 3*dev+2^(a0+1) ≤ (Fintype.card (Wire Pair W) : ℚ) / denom A (Fin a0 → A)) :
    b0*2^a0 ≤ ((Finset.univ : Finset (Wire Pair W)).filter
      (fun w => physicalCell (balancedMask (a0+1) b0) (seat w) = diagCell word)).card := by
  classical
  let c := diagCell word
  let load := ((Finset.univ : Finset (Wire Pair W)).filter
    (fun w => physicalCell (balancedMask (a0+1) b0) (seat w) = c)).card
  have hcount : (load:ℚ) =
      ∑ w : Wire Pair W, indicator (fullCell row col w z) ((cellChartEq A a0).symm c) := by
    dsimp only [load]
    simp_rw [seat_eq]
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, cast_card_eq_indicator]
    apply Finset.sum_congr rfl
    intro w _
    unfold wordLabel indicator
    by_cases h : fullCell row col w z = (cellChartEq A a0).symm c
    · rw [h,Equiv.apply_symm_apply]
      simp
    · have hn : (cellChartEq A a0) (fullCell row col w z) ≠ c :=
        fun he => h ((Equiv.eq_symm_apply _).2 he)
      simp [h,hn]
  have hx := hdev ((cellChartEq A a0).symm c)
  rw [← hcount] at hx
  exact dense_of_rounded_deviation _ _ he hx hp hbig (by rw [pow_succ]; omega)

#print axioms diagonal_load_from_source_variance
end SourceOccupancy

#print axioms dense_of_rounded_deviation

#print axioms diagonal_packet_card
#print axioms diagonal_cell_uniform
#print axioms exists_dense_actual_diagonal_page
end
end P6Joint
