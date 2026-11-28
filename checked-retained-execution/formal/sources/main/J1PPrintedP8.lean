import J1PPrintedMesh
import PaddingBounds
import RandomEndpoint

/-! Finite replacements for the native P8–P11 asymptotic losses. -/

namespace J1PPrinted

theorem printed_padding_slack {C : Type*} (cells : Finset C) (load : C → ℕ)
    (s M d : ℕ) (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (active : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M)
    (hCells : cells.card = stepD (Nat.clog 2 s) d)
    (hMass : ∑ c ∈ cells, load c = M)
    (hColl : PaddingBounds.collision cells load M ≤ 2*(M:ℝ)*sourceDelta s) :
    let L := stepL (Nat.clog 2 s) d
    let u := J9PrintedSchedule.rootU (Nat.clog 2 s)
    let P := PaddingBounds.packetCount cells load L
    (M:ℝ) ≤ (P:ℝ)*L ∧
      (2:ℝ)^u*L*((P:ℝ)*L-M) ≤ 2*M ∧ (P:ℝ)*L ≤ 2*M := by
  dsimp only
  let lam := Nat.clog 2 s
  let u := J9PrintedSchedule.rootU lam
  let L := stepL lam d
  let D := stepD lam d
  let P := PaddingBounds.packetCount cells load L
  let A : ℝ := (2:ℝ)^u*(L:ℝ)*(D:ℝ)
  let S : ℝ := Real.sqrt (2*(M:ℝ)*(sourceDelta s:ℝ))
  have hp : 0<L := stepL_pos lam d
  have hc : 0<cells.card := hCells.symm ▸ stepD_pos lam d
  have hPad := PaddingBounds.p8_collision_padding cells load M (sourceDelta s) L hp hc hMass hColl
  have hn : (M:ℝ) ≤ (P:ℝ)*L := by exact_mod_cast hPad.1
  have hrange := mesh_margins s M d hU active
  dsimp only at hrange
  have hA : A^2 * 2 * (sourceDelta s:ℝ) ≤ M := by
    dsimp [A]
    exact_mod_cast hrange.2.2.2.1
  have hB : A*(L:ℝ) ≤ M := by
    have h0 : (2:ℝ)^u*(L:ℝ)^2*(D:ℝ) ≤ M := by exact_mod_cast hrange.2.2.2.2.1
    calc
      _ = (2:ℝ)^u*(L:ℝ)^2*(D:ℝ) := by dsimp [A]; ring
      _ ≤ _ := h0
  have hS : A*S ≤ M := by
    apply (pow_le_pow_iff_left₀
      (show (0:ℝ)≤A*S by dsimp [A,S]; positivity)
      (show (0:ℝ)≤M by positivity) (by decide : (2:ℕ)≠0)).mp
    calc
      _ = A^2*2*(sourceDelta s:ℝ)*(M:ℝ) := by
        rw [mul_pow]
        dsimp only [S]
        rw [Real.sq_sqrt (by positivity)]
        ring
      _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hA (show (0:ℝ)≤M by positivity)]
  have hm : (P:ℝ)*(L:ℝ)-M ≤ (D:ℝ)*(S+L) := by
    simpa only [hCells] using hPad.2
  let B : ℝ := (2:ℝ)^u*(L:ℝ)
  have hBA : B*(D:ℝ)=A := rfl
  have hT : B*((P:ℝ)*L-M) ≤ 2*M := by
    calc
      _ ≤ B*((D:ℝ)*(S+L)) := mul_le_mul_of_nonneg_left hm (by dsimp [B]; positivity)
      _ = A*S + A*L := by rw [← mul_assoc,hBA,mul_add]
      _ ≤ _ := by linarith
  have hTwo : (2:ℝ)≤B := by
    have hu : 1≤u := hU
    have hu' : (2:ℝ) ≤ (2:ℝ)^u := by
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hu
    have hl : (1:ℝ)≤L := by exact_mod_cast hp
    calc
      _ ≤ (2:ℝ)^u := hu'
      _ = (2:ℝ)^u*1 := (mul_one _).symm
      _ ≤ B := mul_le_mul_of_nonneg_left hl (by positivity)
  have hi := (mul_le_mul_of_nonneg_right hTwo (sub_nonneg.mpr hn)).trans hT
  exact ⟨hn,hT,by linarith⟩

/-- P9 losses, in finite relative form. The original randomized-then-
derandomized physical layout theorem supplies the displayed additive
hypothesis on K. -/
theorem printed_guard_retains (s M d : ℕ)
    (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (active : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M)
    (K : ℝ)
    (guard :
      let L := stepL (Nat.clog 2 s) d
      let D := stepD (Nat.clog 2 s) d
      (M:ℝ)/(2*L) ≤ K + Real.sqrt (5*(M:ℝ)/L) +
        Real.sqrt ((D:ℝ)*(5*(M:ℝ)/L))) :
    let L := stepL (Nat.clog 2 s) d
    let u := J9PrintedSchedule.rootU (Nat.clog 2 s)
    (1-1/(2:ℝ)^u) * ((M:ℝ)/(2*L)) ≤ K := by
  dsimp only at guard ⊢
  let lam := Nat.clog 2 s
  let u := J9PrintedSchedule.rootU lam
  let L := stepL lam d
  let D := stepD lam d
  let B : ℝ := 2^(u+2)
  let X : ℝ := (M:ℝ)/L
  have hL : (0:ℝ)<L := by exact_mod_cast stepL_pos lam d
  have hD : (1:ℝ)≤D := by exact_mod_cast stepD_pos lam d
  have hp : 0<B := by dsimp [B]; positivity
  have hX : 0≤X := by dsimp [X]; positivity
  have hm := mesh_margins s M d hU active
  dsimp only at hm
  have h0 : 5*B^2*(D:ℝ)*L ≤ M := by dsimp [B]; exact_mod_cast hm.2.2.2.2.2
  have hbound : 5*B^2*(D:ℝ) ≤ X := (le_div_iff₀ hL).2 h0
  have hvar : B*Real.sqrt ((D:ℝ)*(5*X)) ≤ X := by
    apply (pow_le_pow_iff_left₀ (by positivity) hX (by decide : (2:ℕ)≠0)).mp
    calc
      _ = (5*B^2*(D:ℝ))*X := by rw [mul_pow,Real.sq_sqrt (by positivity)]; ring
      _ ≤ X*X := mul_le_mul_of_nonneg_right hbound hX
      _ = _ := by ring
  have hvar' : B*Real.sqrt (5*X) ≤ X := by
    have hx : 5*X ≤ (D:ℝ)*(5*X) := by nlinarith
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hx) hp.le).trans hvar
  have hsum : B * (Real.sqrt (5*X)+Real.sqrt ((D:ℝ)*(5*X))) ≤ 2*X := by
    rw [mul_add]
    linarith
  have hsum' : Real.sqrt (5*X)+Real.sqrt ((D:ℝ)*(5*X)) ≤ 2*X/B :=
    (le_div_iff₀ hp).2 (by rw [mul_comm]; exact hsum)
  have hg : X/2 ≤ K + Real.sqrt (5*X) + Real.sqrt ((D:ℝ)*(5*X)) := by
    have h1 : X/2 = (M:ℝ)/(2*L) := by dsimp [X]; ring
    have h2 : (5*X) = 5*(M:ℝ)/L := by dsimp [X]; ring
    rw [h1,h2]
    exact guard
  change (1-1/(2:ℝ)^u) * ((M:ℝ)/(2*L)) ≤ K
  have hx : (M:ℝ)/(2*L) = X/2 := by dsimp [X]; ring
  have hB : B = 4*(2:ℝ)^u := by dsimp [B]; rw [pow_add]; ring
  have he : (1-1/(2:ℝ)^u)*(X/2) = X/2-2*X/B := by
    rw [hB]; ring
  rw [hx,he]
  linarith

/-- Total true slot mass together with the mesh bound forces enough
packets per ordered cell for the P11 relative mean correction. -/
theorem printed_p11_repetitions (s M d b : ℕ)
    (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (active : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M)
    (pad : M ≤ b * stepL (Nat.clog 2 s) d * stepD (Nat.clog 2 s) d) :
    (stepL (Nat.clog 2 s) d)^2 ≤ b := by
  let L := stepL (Nat.clog 2 s) d
  let D := stepD (Nat.clog 2 s) d
  have hm := (mesh_margins s M d hU active).2.1
  have hh : L^2*(L*D) ≤ b*(L*D) := by
    calc
      _ = L^3*D := by ring
      _ ≤ M := hm
      _ ≤ b*L*D := pad
      _ = _ := mul_assoc _ _ _
  exact Nat.le_of_mul_le_mul_right hh
    (Nat.mul_pos (stepL_pos _ _) (stepD_pos _ _))

#print axioms printed_padding_slack
#print axioms printed_guard_retains
#print axioms printed_p11_repetitions

end J1PPrinted

