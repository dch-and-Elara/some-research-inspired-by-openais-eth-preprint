import J1PPrintedP8

/-! The finite P11 variance interface with the actual printed padding. -/

namespace J1PPrinted

theorem printed_p11_numeric {C : Type*} (cells : Finset C) (load : C → ℕ)
    (s M d : ℕ) (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (active : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M)
    (hCells : cells.card = stepD (Nat.clog 2 s) d)
    (hMass : ∑ c ∈ cells, load c = M)
    (hColl : PaddingBounds.collision cells load M ≤ 2*(M:ℝ)*sourceDelta s) :
    let L := stepL (Nat.clog 2 s) d
    let D := stepD (Nat.clog 2 s) d
    let H := PaddingBounds.paddedLoad (cells.sup load) L
    let P := PaddingBounds.packetCount cells load L
    L^2 ≤ PaddingBounds.blocks (cells.sup load) L ∧
      4*(H:ℚ)*(P:ℚ) ≤ 64*(L:ℚ)^3/(D:ℚ)*((M:ℚ)/(2*(L:ℚ)^2))^2 ∧
      1-128*(L:ℚ)^7/(D:ℚ) = 1-128/(L:ℚ)^5 := by
  dsimp only
  let lam := Nat.clog 2 s
  let L := stepL lam d
  let D := stepD lam d
  let b := PaddingBounds.blocks (cells.sup load) L
  let H := PaddingBounds.paddedLoad (cells.sup load) L
  let P := PaddingBounds.packetCount cells load L
  have hPL : P*L=H*D := by simp [P,H,PaddingBounds.packetCount,PaddingBounds.paddedLoad,hCells]; ring
  have hHD : H*D=b*L*D := rfl
  have h := printed_padding_slack cells load s M d hU active hCells hMass hColl
  dsimp only at h
  have hMassPL : M ≤ P*L := by exact_mod_cast h.1
  have hb := printed_p11_repetitions s M d b hU active (hMassPL.trans_eq (hPL.trans hHD))
  have hP : (0:ℚ)≤P := by positivity
  have hL : (0:ℚ)<L := by exact_mod_cast stepL_pos lam d
  have hD : (0:ℚ)<D := by exact_mod_cast stepD_pos lam d
  have he : (P:ℚ)*(L:ℚ)=(H:ℚ)*(D:ℚ) := by exact_mod_cast hPL
  have hPLe : P*L ≤ 2*M := by exact_mod_cast h.2.2
  have hPLe' : (P:ℚ)*(L:ℚ) ≤ 2*(M:ℚ) := by exact_mod_cast hPLe
  refine ⟨hb, RandomEndpoint.relative_variance_bound (H:ℚ) (P:ℚ) (L:ℚ) M D hP hL hD he hPLe', ?_⟩
  have hDpower : (D:ℚ)=(L:ℚ)^12 := by exact_mod_cast stepD_power lam d
  change 1-128*(L:ℚ)^7/(D:ℚ) = 1-128/(L:ℚ)^5
  rw [hDpower]
  field_simp

#print axioms printed_p11_numeric
end J1PPrinted

