import RootPacking
import RootParameters
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Sqrt

namespace RootSeparation

open Entry S11 SourceDensity GraphCutMoments

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : Finset (V × V))

abbrev rootU := retained (size E) 0
abbrev rootA := labelLength (size E) 0
abbrev rootL := packetLength (size E) 0
abbrev rootM := Fintype.card (Wire E)

noncomputable def rootCell (reg : ∀ v, degree E v = 3) : Wire E → RootCell (rootA E) :=
  cellAt (row E reg) (column E) (selectedLabels (row E reg) (column E) (fun _ => 0))

noncomputable abbrev RootPackets (reg : ∀ v, degree E v = 3) :=
  S8.Packet (Fin (rootA E)) (Fin 64) (exactPad (rootCell E reg))

/-- Enough for the numerical root tests. A finite implementation cutoff
may be added separately without changing the eventual statement. -/
def bigRoot (N : ℕ) : Prop := 2^131071 < N

theorem bigRoot_n (hn : bigRoot (n (V := V))) : 20 ≤ n (V := V) := by
  have h : (2 : ℕ)^5 ≤ 2^131071 := Nat.pow_le_pow_right (by decide) (by decide)
  unfold bigRoot at hn
  omega

theorem root_lambda (hn : bigRoot (n (V := V))) : 131072 ≤ lambda (size E) := by
  have hs : n (V := V) ≤ size E := by unfold size; omega
  have h : 2^131071 < size E := lt_of_lt_of_le hn hs
  exact (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).2 h

theorem root_certified (reg : ∀ v, degree E v = 3)
    (hn : bigRoot (n (V := V))) :
    0 < rootU E ∧
    ∃ G : Packing (Wire E) (RootPackets E reg) (rootA E) (rootL E),
      G.cell = rootCell E reg ∧
      CollisionCertificate G.cell (degreeEnvelope (size E) : ℚ) ∧
      Fintype.card (RootPackets E reg) * rootL E ≤ 3 * rootM E ∧
      Nonempty (Fin (probeCount (rootM E) (rootL E)) ↪ (Fin (4*lambda (size E)) → Bool)) := by
  classical
  have hdim := (dimensions E reg).2
  have hm : rootM E = 10 * n (V := V) := wire_count E reg
  have hsm : size E ≤ rootM E := by omega
  have hms : rootM E ≤ 3*size E := by omega
  obtain ⟨hu,_,_,hΔ,hfeasible,hslots,_,hp⟩ := root_numeric (root_lambda E hn) hsm hms
  let Δ := degreeEnvelope (size E)
  have hcert : CollisionCertificate (rootCell E reg) (Δ : ℚ) := by
    constructor
    · exact selected_collision _ _ _ Δ (fun v => (row_degree E reg v).trans hΔ)
        (fun p => by rw [col_degree]; omega)
    · rw [← cell_count (size E)] at hfeasible
      exact_mod_cast hfeasible
  rw [← cell_count (size E)] at hslots
  obtain ⟨G,hcell,hpack⟩ := exact_packets (rootCell E reg) Δ hcert hslots
  have hprobe : Nonempty (Fin (probeCount (rootM E) (rootL E)) ↪
      (Fin (4*lambda (size E)) → Bool)) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hp)
  exact ⟨hu,G,hcell,by rwa [hcell],hpack,hprobe⟩

theorem exponent_real (reg : ∀ v, degree E v = 3)
    (hn : 20 ≤ n (V := V)) {d : ℕ}
    (hd : rootM E ≤ 4*(Nat.sqrt (rootU E)+1)*d) :
    (n (V := V) : ℝ) / (2*Real.sqrt (Real.logb 2 (n (V := V)))) ≤ (d : ℝ) := by
  let N := n (V := V)
  let l := lambda (size E)
  let b := Real.logb 2 (N : ℝ)
  have hdim := (dimensions E reg).2
  have hm : rootM E = 10 * n (V := V) := wire_count E reg
  rw [hm] at hd
  have hl : l ≤ Nat.clog 2 N + 2 := by
    apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
    have h := (Nat.clog_le_iff_le_pow (by decide : 1<2)).1
      (le_rfl (a := Nat.clog 2 N))
    rw [pow_add]
    norm_num
    change 2 * size E = 7 * N at hdim
    omega
  have hlp : 0 < Nat.clog 2 N :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).2 (by change 2^0 < n (V := V); omega)
  have hpow : 2 ^ (Nat.clog 2 N - 1) < N :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).1 (by omega)
  have hblog := Real.logb_lt_logb (by norm_num : (1 : ℝ) < 2)
    (show 0 < (2 : ℝ)^(Nat.clog 2 N - 1) by positivity)
    (show (2 : ℝ)^(Nat.clog 2 N - 1) < N by exact_mod_cast hpow)
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one, Nat.cast_sub (by omega : 1 ≤ Nat.clog 2 N)] at hblog
  have hb3 : 3 ≤ b := by
    have h := Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2)
      (show 0 < (2 : ℝ)^3 by positivity)
      (show (2 : ℝ)^3 ≤ N by norm_num; exact_mod_cast (show 8 ≤ N by omega))
    rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
      mul_one] at h
    exact_mod_cast h
  have hll : (l : ℝ) ≤ 2*b := by
    have hl' : (l : ℝ) ≤ (Nat.clog 2 N : ℝ) + 2 := by exact_mod_cast hl
    simp only [Nat.cast_one] at hblog
    change (Nat.clog 2 N : ℝ) - 1 < b at hblog
    linarith
  have hu : rootU E ≤ l := Nat.div_le_self _ _
  have hsq : Nat.sqrt (rootU E) ^ 2 ≤ l := (Nat.sqrt_le' (rootU E)).trans hu
  have hb0 : 0 < b := by linarith
  have hr : (Nat.sqrt (rootU E) : ℝ)^2 ≤ 2*b :=
    (show (Nat.sqrt (rootU E) : ℝ)^2 ≤ l by exact_mod_cast hsq).trans hll
  have hroot : (Nat.sqrt (rootU E) : ℝ) ≤ 2*Real.sqrt b := by
    have h1 := Real.sq_sqrt hb0.le
    by_contra! h
    nlinarith [sq_nonneg (Real.sqrt b), mul_pos (show (0 : ℝ) < 2 by norm_num) hb0,
      mul_pos (sub_pos.mpr h) (show 0 < (Nat.sqrt (rootU E) : ℝ) + 2 * Real.sqrt b by positivity)]
  have hone : 1 ≤ Real.sqrt b := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ b by linarith)
    simpa using h
  have hq : (Nat.sqrt (rootU E) : ℝ)+1 ≤ 4*Real.sqrt b := by linarith
  have hdc : 10*(N : ℝ) ≤ 4*((Nat.sqrt (rootU E) : ℝ)+1)*(d : ℝ) := by exact_mod_cast hd
  have hmult := mul_le_mul_of_nonneg_right hq (show (0 : ℝ) ≤ d by positivity)
  apply (div_le_iff₀ (by change 0 < 2*Real.sqrt b; positivity)).2
  change (N : ℝ) ≤ (d : ℝ) * (2 * Real.sqrt b)
  linarith

#print axioms root_certified
#print axioms exponent_real

end RootSeparation
