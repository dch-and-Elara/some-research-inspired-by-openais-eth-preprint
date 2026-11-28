import P11R12EndpointCapacity

namespace P11R12Scale
open scoped Classical BigOperators
open P11FullPacking P11R12Choice P11R12EndpointCapacity
variable {K : Type*} [LinearOrder K] [Fintype K] {a b : ℕ}

omit [LinearOrder K] in
theorem cells_are_Ltwelve (hK : Fintype.card K = 64) :
    Nat.card (Cell (Fin a) K) = (2^a)^12 := by
  rw [total_cells,hK]
  calc
    (64:ℕ)^(2*a) = ((2:ℕ)^6)^(2*a) := rfl
    _ = (2:ℕ)^(6*(2*a)) := (pow_mul _ _ _).symm
    _ = (2:ℕ)^(a*12) := by congr 1; omega
    _ = ((2:ℕ)^a)^12 := pow_mul _ _ _

/-- Actual count of packet endpoints gives H times total cap, not H
times number of raw legs. The paper uses the stronger estimate 4HP. -/
theorem printed_variance_scale
    [Fintype (Key (Fin a) K)] [∀ k : Key (Fin a) K, Fintype (Packet b k)]
    (ω : Draw a b K) (M : ℕ)
    (hK : Fintype.card K = 64)
    (hSlots : Nat.card (Page a b K) * 2^a ≤ 2*M) :
    let L : ℚ := ((2:ℕ)^a:ℚ)
    let H : ℚ := ((b*2^a:ℕ):ℚ)
    let D : ℚ := (Nat.card (Cell (Fin a) K):ℚ)
    H*(∑ k : Key (Fin a) K, (Nat.card (Packet b k):ℚ)) ≤
      64*L^3/D*((M:ℚ)/(2*L^2))^2 ∧
      1-128*L^7/D = 1-128/L^5 := by
  dsimp only
  let L : ℚ := ((2:ℕ)^a:ℚ)
  let H : ℚ := ((b*2^a:ℕ):ℚ)
  let D : ℚ := (Nat.card (Cell (Fin a) K):ℚ)
  let P : ℚ := (Nat.card (Page a b K):ℚ)
  have hs : P*L=H*D := by
    dsimp [P,L,H,D]
    exact_mod_cast (total_slots (commonMask (b:=b) (masks ω))).trans (Nat.mul_comm _ _)
  have hPD : P*L ≤ 2*(M:ℚ) := by dsimp [P,L]; exact_mod_cast hSlots
  have hD : D = L^12 := by dsimp [D,L]; exact_mod_cast cells_are_Ltwelve (a:=a) hK
  have hL : 0<L := by positivity
  have hPosD : 0<D := by rw [hD]; positivity
  have hPP : (0:ℚ) ≤ P := by positivity
  have heq : (∑ k : Key (Fin a) K, (Nat.card (Packet b k):ℚ)) = P := by
    dsimp [P]
    exact_mod_cast exact_total_packets (a:=a) (b:=b) (K:=K)
  change H*(_ : ℚ) ≤ 64*L^3/D*((M:ℚ)/(2*L^2))^2 ∧
    1-128*L^7/D = 1-128/L^5
  rw [heq]
  refine ⟨?_,?_⟩
  · have hB := RandomEndpoint.relative_variance_bound H P L M D hPP hL hPosD hs hPD
    have hh : 0≤H*P := by positivity
    linarith
  · rw [hD]
    field_simp

#print axioms cells_are_Ltwelve
#print axioms printed_variance_scale
end P11R12Scale
