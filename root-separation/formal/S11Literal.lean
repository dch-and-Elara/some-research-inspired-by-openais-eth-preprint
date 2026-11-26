
import S11Modes
import S11Wires

namespace S11

variable {P W V : Type*} [Fintype P] [Fintype W]
open scoped BigOperators

/-- A batch actually evaluates its children in its own coefficient ring.
    For the printed contraction these rings are O/(2^p_t) at the root. -/
noncomputable def sourceBatch {R : ℤ → Type*} [∀ t, CommSemiring (R t)]
    (B : ℤ → Type*) [∀ t, Fintype (B t)] (M L a u p : ℕ)
    (child : (t : ℤ) → ℕ → List ℕ → Fin 64 → R t) (t : ℤ) (j : ℕ) :
    R t × List Slot :=
  let pt := precision p M a u L t
  foldTuples (modeWeights (B t) (level t) pt) pt
    (fun st β => (st.1 + ((List.finRange 64).map (child t j β)).prod,
      Slot.mk t j β :: st.2)) (0, [])

/-- The ghost trace joins the per-probe accumulators in their execution
    order. The value of each sourceBatch feeds the interpolation stage. -/
noncomputable def sourceTrace {R : ℤ → Type*} [∀ t, CommSemiring (R t)]
    (B : ℤ → Type*) [∀ t, Fintype (B t)] (M L a u p : ℕ)
    (child : (t : ℤ) → ℕ → List ℕ → Fin 64 → R t) : List Slot :=
  (centers u L).toList.flatMap fun t =>
    (List.range (probeCount M L)).flatMap fun j =>
      (sourceBatch B M L a u p child t j).2.reverse

theorem sourceBatch_eq {R : ℤ → Type*} [∀ t, CommSemiring (R t)]
    (B : ℤ → Type*) [∀ t, Fintype (B t)] (M L a u p : ℕ)
    (child : (t : ℤ) → ℕ → List ℕ → Fin 64 → R t) (t : ℤ) (j : ℕ) :
    sourceBatch B M L a u p child t j =
      runBatch (List.finRange 64) (fun b => child t j b.exponents)
        (batch (B t) t j (precision p M a u L t)) := by
  unfold sourceBatch runBatch batch
  rw [foldTuples_eq, List.foldl_map]

theorem sourceTrace_eq_slots {R : ℤ → Type*} [∀ t, CommSemiring (R t)]
    (B : ℤ → Type*) [∀ t, Fintype (B t)] (M L a u p : ℕ)
    (child : (t : ℤ) → ℕ → List ℕ → Fin 64 → R t) :
    sourceTrace B M L a u p child = rootSlots u M L a p B := by
  simp [sourceTrace, sourceBatch_eq, runBatch_trace, rootSlots]

theorem slot_charge {S : Type*} (l : List S) (cost : S → ℕ)
    (hcost : ∀ t ∈ l, 1 ≤ cost t) : l.length ≤ (l.map cost).sum := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    have ht := hcost t (by simp)
    have hrest := ih (fun y hy => hcost y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    omega

private theorem root_length_large {u : ℕ} (hu : 0 < u) : 2 * (Nat.sqrt u + 1) ≤ 2 ^ (2*u) := by
  have h : ∀ k : ℕ, 2*(k+2) ≤ (2 : ℕ) ^ (2*(k+1)) := by
    intro k
    induction k with
    | zero => decide
    | succ k ih =>
      rw [show 2*(k.succ+1) = 2*(k+1)+2 by omega, pow_add]
      norm_num
      omega
  have := h (u-1)
  have hsq := Nat.sqrt_le_self u
  have heq : u - 1 + 1 = u := by omega
  rw [heq] at this
  omega

theorem odd_root_lower {M a L u p : ℕ} (G : Packing W P a L)
    (hwire : Fintype.card W = M) (Δ : ℚ)
    (cert : SourceDensity.CollisionCertificate G.cell Δ)
    (hpack : Fintype.card P * L ≤ 3*M)
    (hM : 0 < M) (hu : 0 < u) (ha : a = 2*u) (hL : L = 2^a) :
    let B := Fintype.card (G.mixedAt 1)
    let d := B * lowWeights u L
    M ≤ 4 * (Nat.sqrt u + 1) * d ∧ 2^d ≤ (rootSlots u M L a p G.mixedAt).length := by
  have hlvl : level 1 = 0 := by simp [level]
  let i : Fin a := ⟨0, by omega⟩
  have hB := G.mixedAt_card 1 i hlvl.symm
  have hcover := G.mixed_capacity i Δ cert
  rw [hwire, ← hB] at hcover
  have hupper := G.mixed_upper i
  rw [← hB] at hupper
  have hLlarge : 2 * (Nat.sqrt u + 1) ≤ L := by
    rw [hL, ha]
    exact root_length_large hu
  have hp := odd_precision_budget p M a u L hu
  have hsmall := lowWeights_budget hM (by omega) ((Nat.mul_le_mul_right L hupper).trans hpack)
    hcover hp
  refine ⟨lowWeights_exponent hcover hLlarge, ?_⟩
  have hcount := small_modes_lower (B := G.mixedAt 1) (i := level 1) hsmall.1 hsmall.2
  have hb := batch_le_root u M L a p G.mixedAt (one_active hu (by omega : 1 < L))
    (j := 0) (by simp [probeCount])
  unfold batch at hb
  rw [List.length_map] at hb
  exact hcount.trans hb

theorem threshold_le_size (s : ℕ) (hs : 0 < Nat.sqrt (lambda s)) :
    leafThreshold s ≤ s := by
  unfold leafThreshold ceilDiv
  apply Nat.lt_succ_iff.1
  apply (Nat.div_lt_iff_lt_mul hs).2
  have h := Nat.mul_le_mul_left s hs
  rw [Nat.mul_one] at h
  rw [Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul]
  omega

theorem cloned_root_active {s N n m : ℕ} (hn : n = 4*N) (hm : 2*m = 13*N)
    (hs : s = n + m) (hN : 0 < N) (hu : 0 < retained s 0) :
    leafThreshold s < 24*N := by
  have hl : 0 < lambda s := by
    by_contra! h
    have he : lambda s = 0 := by omega
    simp [retained, he] at hu
  have hsqrt : 0 < Nat.sqrt (lambda s) := Nat.sqrt_pos.2 hl
  have hh := threshold_le_size s hsqrt
  omega

variable [Fintype V] [DecidableEq V]

noncomputable abbrev clonedSize (E : Finset (V × V)) (regular : ∀ v, GraphCutMoments.degree E v = 3)
    (σ : V → Bool) : ℕ := Fintype.card (V × Fin 4) + (cloned E regular σ).length

theorem cloned_branch_reached {s N n m : ℕ} (hn : n = 4*N) (hm : 2*m = 13*N)
    (hs : s = n + m) (hu : 0 < retained s 0) : clauseBranch n m := by
  apply cloned_dispatch hn hm
  have h4 : 4 < n := by
    by_contra! h
    have h16 : s ≤ 2^4 := by norm_num; omega
    have hl := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 h16
    have hsmall : lambda s < 131072 * 2^0 := by
      norm_num [lambda]
      omega
    unfold retained at hu
    rw [Nat.div_eq_of_lt hsmall] at hu
    omega
  have hnlog : 2 < Nat.clog 2 n :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 h4
  exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by omega : 2^1 < _)

/-- Finite source-instance lower bound. The same certificate applies to
    every pin sign assignment and every choice of correct child evaluator.
    Packing can be instantiated separately for each input as well. -/
theorem cloned_literal_root_lower (E : Finset (V × V))
    (regular : ∀ v, GraphCutMoments.degree E v = 3) (σ : V → Bool)
    (hu : 0 < retained (clonedSize E regular σ) 0)
    (hN : 0 < Fintype.card V)
    {R : ℤ → Type*} [∀ t, CommSemiring (R t)]
    (child : (t : ℤ) → ℕ → List ℕ → Fin 64 → R t)
    (G : Packing (Wire (cloned E regular σ)) P (labelLength (clonedSize E regular σ) 0)
      (packetLength (clonedSize E regular σ) 0))
    (Δ : ℚ) (cert : SourceDensity.CollisionCertificate G.cell Δ)
    (hpack : Fintype.card P * packetLength (clonedSize E regular σ) 0 ≤ 3 * (24 * Fintype.card V)) :
    let s := clonedSize E regular σ
    let M := 24 * Fintype.card V
    let p := Fintype.card (V × Fin 4) + 1
    let d := Fintype.card (G.mixedAt 1) * lowWeights (retained s 0) (packetLength s 0)
    clauseBranch (Fintype.card (V × Fin 4)) (cloned E regular σ).length ∧
    leafThreshold s < M ∧
    M ≤ 4 * (Nat.sqrt (retained s 0) + 1) * d ∧
    2^d ≤ (sourceTrace G.mixedAt M (packetLength s 0) (labelLength s 0)
      (retained s 0) p child).length := by
  obtain ⟨hn,hm⟩ := cloned_dimensions E regular σ
  dsimp only
  rw [sourceTrace_eq_slots]
  refine ⟨cloned_branch_reached hn hm rfl hu, cloned_root_active hn hm rfl hN hu, ?_⟩
  exact odd_root_lower G (cloned_wire_count E regular σ) Δ cert hpack (by omega)
    hu (root_parameters (clonedSize E regular σ)).1 rfl

/-- The direct edge scan makes the input-family quantifier essential.
    This fold makes one visit per stored edge. -/
noncomputable def edgeScan (E : Finset (V × V)) (σ : V → Bool) : Bool := by
  classical
  exact E.toList.all (fun e => σ e.1 || σ e.2)

theorem edgeScan_count (E : Finset (V × V)) (regular : ∀ v, GraphCutMoments.degree E v = 3)
    (σ : V → Bool) : contraction (cloned E regular σ) = (edgeScan E σ).toNat := by
  classical
  rw [cloned_contraction, PinnedCNF.count_eq_indicator]
  unfold edgeScan
  cases h : E.toList.all (fun e => σ e.1 || σ e.2)
  · have hn : ¬ PinnedCNF.AllEdges E σ := by
      intro hc
      have ht : E.toList.all (fun e => σ e.1 || σ e.2) = true := by
        simpa [List.all_eq_true, PinnedCNF.AllEdges] using hc
      rw [ht] at h
      contradiction
    simp [hn]
  · have ht : PinnedCNF.AllEdges E σ := by
      simpa [List.all_eq_true, PinnedCNF.AllEdges] using h
    simp [ht]

#print axioms sourceBatch_eq
#print axioms sourceTrace_eq_slots
#print axioms slot_charge
#print axioms odd_root_lower
#print axioms cloned_root_active
#print axioms cloned_branch_reached
#print axioms cloned_literal_root_lower
#print axioms edgeScan_count

end S11

