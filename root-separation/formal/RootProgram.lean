import RootLayout
import RootGraphs
import S11Probes
import S11Lift

/-! The literal implementation described by reduction:363–369 and
contraction:475–482, 487–523, 560–567, 603–613.
The only charged component is one fixed-width coordinate of each root
accumulation. Child result values and all other work are parametric. -/

namespace RootSeparation

open Entry S11 SourceDensity GraphCutMoments

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : Finset (V × V))

noncomputable def chosenPacking (reg : ∀ v, degree E v = 3)
    (hn : bigRoot (n (V := V))) :
    Packing (Wire E) (RootPackets E reg) (rootA E) (rootL E) :=
  Classical.choose (root_certified E reg hn).2

theorem chosenPacking_spec (reg : ∀ v, degree E v = 3)
    (hn : bigRoot (n (V := V))) :
    (chosenPacking E reg hn).cell = rootCell E reg ∧
    CollisionCertificate (chosenPacking E reg hn).cell (degreeEnvelope (size E) : ℚ) ∧
    Fintype.card (RootPackets E reg) * rootL E ≤ 3 * rootM E := by
  have h := Classical.choose_spec (root_certified E reg hn).2
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem chosenPacking_group_quota (reg : ∀ v, degree E v = 3)
    (hn : bigRoot (n (V := V))) (j : Fin (rootA E)) (b : Bool) (g : Fin 64) :
    let cell := (chosenPacking E reg hn).cell
    (fiberCount (fun w => (if b then (cell w).2 else (cell w).1) j) g : ℚ) ≤
      3 * rootM E / 64 :=
  packet_group_quota _ _ (chosenPacking_spec E reg hn).2.1 j b g

theorem probes_fit (reg : ∀ v, degree E v = 3)
    (hn : bigRoot (n (V := V))) : probeCount (rootM E) (rootL E) ≤ 2^(4*lambda (size E)) := by
  have hm : rootM E = 10 * n (V := V) := wire_count E reg
  have hs := (dimensions E reg).2
  exact root_probe_capacity (by omega) (root_certified E reg hn).1

def probe (reg : ∀ v, degree E v = 3) (hn : bigRoot (n (V := V))) :
    Fin (probeCount (rootM E) (rootL E)) ↪ BitVec (4*lambda (size E)) :=
  let h := probes_fit E reg hn
  ⟨binaryProbe _ _ h, binaryProbe_injective _ _ h⟩

abbrev nativePrecision (t : ℤ) :=
  precision (initialPrecision (V := V)) (rootM E) (rootA E) (rootU E) (rootL E) t

abbrev NativeChild (O : Type*) [CommRing O] :=
  (t : ℤ) → ℕ → List ℕ → Fin 64 → ModTwoPow O (nativePrecision E t)

/-- Count only active sparse-root operations beyond a possible fixed finite
exceptional range K. The dispatcher is applied to the actual pinned CNF.
K is a cutoff on s, supplied by the chosen reading of the finite exceptions. -/
noncomputable def runEvents {O : Type*} [CommRing O]
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) (K : ℕ)
    (child : NativeChild E O) : List Slot := by
  classical
  exact if hn : bigRoot (n (V := V)) then
    if dispatch (simpleNormalize (PinnedCNF.formula E σ)) = .sparse ∧ K < size E ∧
        leafThreshold (size E) < rootM E then
      sourceTrace (chosenPacking E reg hn).mixedAt (rootM E) (rootL E) (rootA E)
        (rootU E) (initialPrecision (V := V)) child
    else []
  else []

theorem runEvents_active {O : Type*} [CommRing O]
    (simple : Simple E) (reg : ∀ v, degree E v = 3) (σ : V → Bool) (K : ℕ)
    (child : NativeChild E O) (hn : bigRoot (n (V := V))) (hK : K < size E) :
    runEvents E reg σ K child =
      sourceTrace (chosenPacking E reg hn).mixedAt (rootM E) (rootL E) (rootA E)
        (rootU E) (initialPrecision (V := V)) child := by
  have hn' := bigRoot_n hn
  have hh : leafThreshold (size E) < rootM E := root_active E reg (by omega)
  rw [runEvents, dif_pos hn, simpleNormalize_pinned E simple σ,
    if_pos ⟨dispatch_pinned E reg σ hn',hK,hh⟩]

theorem runEvents_iff {O : Type*} [CommRing O]
    (simple : Simple E) (reg : ∀ v, degree E v = 3) (σ : V → Bool) (K : ℕ)
    (child : NativeChild E O) (hn : bigRoot (n (V := V))) (hK : K < size E)
    (t : ℤ) (j : ℕ) (β : List ℕ) :
    let pt := nativePrecision E t
    let weights := modeWeights ((chosenPacking E reg hn).mixedAt t) (level t) pt
    Slot.mk t j β ∈ runEvents E reg σ K child ↔
      t ∈ centers (rootU E) (rootL E) ∧ j < probeCount (rootM E) (rootL E) ∧
      β.length = weights.length ∧ weightSum weights β < pt := by
  rw [runEvents_active E simple reg σ K child hn hK]
  exact sourceTrace_mem_iff _ _ _ _ _ _ child t j β

noncomputable def runBitWork {O : Type*} [CommRing O]
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) (K : ℕ)
    (child : NativeChild E O) (acc term : Slot → ℕ) (otherWork : ℕ) : ℕ :=
  accumulatorBitWork (initialPrecision (V := V)) (rootM E) (rootA E) (rootU E)
    (rootL E) (runEvents E reg σ K child) acc term + otherWork

theorem pinned_finite_work {O : Type*} [CommRing O]
    (simple : Simple E) (reg : ∀ v, degree E v = 3) (σ : V → Bool) (K : ℕ)
    (child : NativeChild E O) (acc term : Slot → ℕ) (otherWork : ℕ)
    (hn : bigRoot (n (V := V))) (hK : K < size E) :
    ∃ d, 10 * n (V := V) ≤ 4*(Nat.sqrt (rootU E)+1)*d ∧
      2^d ≤ runBitWork E reg σ K child acc term otherWork := by
  have hpos : 0 < rootM E := by
    have hn' := bigRoot_n hn
    have hm : rootM E = 10 * n (V := V) := wire_count E reg
    omega
  let G := chosenPacking E reg hn
  obtain ⟨_,hc,hp⟩ := chosenPacking_spec E reg hn
  obtain ⟨hsize,hwork⟩ := literal_root_bits G rfl (degreeEnvelope (size E) : ℚ) hc hp hpos
    (root_certified E reg hn).1 (root_parameters (size E)).1 rfl
    (Nat.succ_pos (n (V := V))) child acc term
  refine ⟨Fintype.card (G.mixedAt 1) * lowWeights (rootU E) (rootL E), ?_, ?_⟩
  · rw [← wire_count E reg]
    exact hsize
  · rw [runBitWork, runEvents_active E simple reg σ K child hn hK]
    exact hwork.trans (Nat.le_add_right _ _)

/-- c = 1/2, base-two logarithm, every sufficiently large simple cubic input
and every sign vector. The hypothesis on K only excludes a fixed finite range. -/
theorem pinned_literal_program_lower {O : Type*} [CommRing O]
    (simple : Simple E) (reg : ∀ v, degree E v = 3) (σ : V → Bool) (K : ℕ)
    (child : NativeChild E O) (acc term : Slot → ℕ) (otherWork : ℕ)
    (hn : max (2^131071) K < n (V := V)) :
    (2 : ℝ) ^ ((n (V := V) : ℝ) / (2 * Real.sqrt (Real.logb 2 (n (V := V))))) ≤
      (runBitWork E reg σ K child acc term otherWork : ℝ) := by
  have hN : bigRoot (n (V := V)) := (le_max_left _ _).trans_lt hn
  have hK : K < size E := ((le_max_right _ _).trans_lt hn).trans_le (by unfold size; omega)
  obtain ⟨d,hd,hwork⟩ := pinned_finite_work E simple reg σ K child acc term otherWork hN hK
  have hM : rootM E ≤ 4*((rootU E).sqrt+1)*d := by
    rwa [show rootM E = 10 * n (V := V) from wire_count E reg]
  have hExp := exponent_real E reg (bigRoot_n hN) hM
  calc
    _ ≤ (2 : ℝ) ^ (d : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hExp
    _ ≤ _ := by rw [Real.rpow_natCast]; exact_mod_cast hwork

#check @pinned_literal_program_lower
#check @chosenPacking_spec
#check @runEvents_active
#print axioms chosenPacking_spec
#print axioms chosenPacking_group_quota
#print axioms probe
#print axioms runEvents_active
#print axioms runEvents_iff
#print axioms pinned_finite_work
#print axioms pinned_literal_program_lower

end RootSeparation
