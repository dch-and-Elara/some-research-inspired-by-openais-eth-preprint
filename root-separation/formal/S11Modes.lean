
import S11Schedule
import SourceDensity

namespace S11

open scoped BigOperators

/-- Appendix D packet placement. The unordered pair at each coordinate is
    fixed by the packet, with the orientation given by its slot bit. -/
structure Packing (W P : Type*) [Fintype P] (a L : ℕ) where
  position : W ↪ P × Fin L
  cell : W → (Fin a → Fin 64) × (Fin a → Fin 64)
  pair : P → Fin a → Fin 64 × Fin 64
  orientation : ∀ w i,
    ( (cell w).1 i, (cell w).2 i ) =
      if (position w).2.val.testBit i.val then (pair (position w).1 i).swap
      else pair (position w).1 i

abbrev Packing.Mixed {W P : Type*} [Fintype P] {a L : ℕ} (G : Packing W P a L)
    (i : Fin a) := {z : P // (G.pair z i).1 ≠ (G.pair z i).2}

def Packing.mixedAt {W P : Type*} [Fintype P] {a L : ℕ}
    (G : Packing W P a L) (t : ℤ) :=
  {z : P // ∃ i : Fin a, i.val = level t ∧ (G.pair z i).1 ≠ (G.pair z i).2}

noncomputable instance mixedAtFintype {W P : Type*} [Fintype P] {a L : ℕ}
    (G : Packing W P a L) (t : ℤ) : Fintype (G.mixedAt t) := by
  classical
  unfold Packing.mixedAt
  infer_instance

theorem Packing.mixedAt_card {W P : Type*} [Fintype P] {a L : ℕ}
    (G : Packing W P a L) (t : ℤ) (i : Fin a) (hi : i.val = level t) :
    Fintype.card (G.mixedAt t) = Fintype.card (G.Mixed i) := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro z
  constructor
  · rintro ⟨j,hj,hm⟩
    have hji : j = i := Fin.ext (hj.trans hi.symm)
    simpa [hji] using hm
  · intro hm
    exact ⟨i,hi,hm⟩

private abbrev Cell (a : ℕ) := (Fin a → Fin 64) × (Fin a → Fin 64)
private def diagonal {a : ℕ} (i : Fin a) (c : Cell a) : Prop := c.1 i = c.2 i

private def cellEquiv {a : ℕ} (i : Fin a) : Cell a ≃ ({c : Cell a // diagonal i c} × Fin 64) where
  toFun c := (⟨(c.1, Function.update c.2 i (c.1 i)), by simp [diagonal]⟩, c.2 i)
  invFun j := (j.1.val.1, Function.update j.1.val.2 i j.2)
  left_inv c := by
    refine Prod.ext rfl ?_
    change Function.update (Function.update c.2 i (c.1 i)) i (c.2 i) = c.2
    funext k
    by_cases h : k = i <;> simp [h, Function.update]
  right_inv j := by
    apply Prod.ext
    · apply Subtype.ext
      refine Prod.ext rfl ?_
      change Function.update (Function.update j.1.val.2 i j.2) i (j.1.val.1 i) = j.1.val.2
      funext k
      have hdiag := j.1.property
      change j.1.val.1 i = j.1.val.2 i at hdiag
      by_cases h : k = i <;> simp [h, Function.update, hdiag]
    · simp

theorem Packing.mixed_capacity {W P : Type*} [Fintype W] [Fintype P] {a L : ℕ}
    (G : Packing W P a L) (i : Fin a) (Δ : ℚ)
    (cert : SourceDensity.CollisionCertificate G.cell Δ) :
    Fintype.card W ≤ 2 * (Fintype.card (G.Mixed i) * L) := by
  classical
  let d := fun c : Cell a => decide (diagonal i c)
  have hdiag : Fintype.card {c : Cell a // diagonal i c} * 64 = Fintype.card (Cell a) := by
    simpa using (Fintype.card_congr (cellEquiv i)).symm
  have hcard : ((Finset.univ.filter fun c => d c = true).card : ℚ) * 64 =
      Fintype.card (Cell a) := by
    have hnat : (Finset.univ.filter fun c => d c = true).card =
        Fintype.card {c : Cell a // diagonal i c} := by
      rw [Fintype.card_subtype (p := diagonal i)]
      congr 1
      ext c
      simp [d]
    rw [hnat]
    exact_mod_cast hdiag
  have hQ : (0 : ℚ) < Fintype.card (Cell a) := by exact_mod_cast Fintype.card_pos
  have hload : (SourceDensity.fiberCount (fun w => d (G.cell w)) true : ℚ) ≤
      (Fintype.card W : ℚ) / 32 := by
    rw [SourceDensity.fiberCount_comp, Nat.cast_sum]
    calc
      _ ≤ ∑ _ ∈ Finset.univ.filter (fun c => d c = true),
          2 * (Fintype.card W : ℚ) / Fintype.card (Cell a) :=
        Finset.sum_le_sum fun c _ => SourceDensity.port_cell_bound G.cell Δ cert c
      _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        rw [← hcard]
        have hn : (0 : ℚ) < (Finset.univ.filter fun c => d c = true).card := by linarith
        field_simp
        ring
  have heq : Fintype.card {w // diagonal i (G.cell w)} =
      SourceDensity.fiberCount (fun w => d (G.cell w)) true := by
    rw [Fintype.card_subtype, SourceDensity.fiberCount]
    congr 1
    ext w
    simp [d]
  have hd : 32 * Fintype.card {w // diagonal i (G.cell w)} ≤ Fintype.card W := by
    rw [heq]
    have hh := (le_div_iff₀ (by norm_num : (0 : ℚ) < 32)).1 hload
    rw [mul_comm] at hh
    exact_mod_cast hh
  have hinj : Fintype.card {w // ¬ diagonal i (G.cell w)} ≤
      Fintype.card (G.Mixed i × Fin L) := by
    let f (w : {w // ¬ diagonal i (G.cell w)}) : G.Mixed i × Fin L :=
      (⟨(G.position w.val).1, by
        intro he
        apply w.property
        have ho := G.orientation w.val i
        unfold diagonal
        split at ho <;> simpa [he, Prod.mk.injEq, Prod.swap] using
          (congrArg (fun x : Fin 64 × Fin 64 => x.1 = x.2) ho).mpr (by simp [he])⟩,
       (G.position w.val).2)
    apply Fintype.card_le_of_injective f
    intro x y hxy
    apply Subtype.ext
    apply G.position.injective
    exact congrArg (fun z : G.Mixed i × Fin L => (z.1.val, z.2)) hxy
  rw [Fintype.card_prod, Fintype.card_fin] at hinj
  rw [Fintype.card_subtype_compl] at hinj
  omega

theorem Packing.mixed_upper {W P : Type*} [Fintype P] {a L : ℕ}
    (G : Packing W P a L) (i : Fin a) :
    Fintype.card (G.Mixed i) ≤ Fintype.card P :=
  Fintype.card_le_of_injective Subtype.val Subtype.val_injective

private theorem weightSum_map {T : Type*} (l : List T) (w b : T → ℕ) :
    weightSum (l.map w) (l.map b) = (l.map fun x => w x * b x).sum := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [weightSum, ih]

private theorem modeMask_le {B : Type*} [Fintype B] {i p k : ℕ} (hk : k ≤ p - 1) :
    2 ^ (Fintype.card B * k) ≤ (tuples (modeWeights B i p) p).length
    ∨ p ≤ Fintype.card B * k * k := by
  classical
  by_cases hbudget : p ≤ Fintype.card B * k * k
  · exact Or.inr hbudget
  left
  let sm : B × Fin k ↪ Mode B i p :=
    ⟨fun b => (b.1, ⟨0, by positivity⟩, ⟨b.2.val, lt_of_lt_of_le b.2.isLt hk⟩),
      fun b c h => Prod.ext (congrArg (fun m : Mode B i p => m.1) h) (Fin.ext (congrArg (fun m => m.2.2.val) h))⟩
  let small := (Finset.univ : Finset (B × Fin k)).map sm
  let encode (x : B × Fin k → Bool) (m : Mode B i p) : ℕ :=
    if h : ∃ j, sm j = m then (x (Classical.choose h)).toNat else 0
  have encode_image (x : B × Fin k → Bool) (j : B × Fin k) :
      encode x (sm j) = (x j).toNat := by
    have h : ∃ z, sm z = sm j := ⟨j,rfl⟩
    change (if h' : ∃ j', sm j' = sm j then (x (Classical.choose h')).toNat else 0) = _
    rw [dif_pos h, sm.injective (Classical.choose_spec h)]
  have bound (x : B × Fin k → Bool) (m : Mode B i p) :
      (m.2.2.val + 1) * encode x m ≤ if m ∈ small then k else 0 := by
    by_cases h : ∃ j, sm j = m
    · obtain ⟨j, rfl⟩ := h
      rw [encode_image, if_pos (Finset.mem_map.2 ⟨j,Finset.mem_univ _,rfl⟩)]
      have hj := j.2.isLt
      cases x j <;> simp [sm] <;> omega
    · have hn : m ∉ small := fun hm =>
        let ⟨j, _, h⟩ := Finset.mem_map.1 hm
        ‹¬ ∃ j, sm j = m› ⟨j,h⟩
      change _ * (if h' : ∃ j, sm j = m then (x (Classical.choose h')).toNat else 0) ≤ _
      rw [dif_neg h, if_neg hn, mul_zero]
  let vector := fun x => (modes B i p).map (encode x)
  have hv (x) : vector x ∈ tuples (modeWeights B i p) p := by
    have hw : ∀ w ∈ modeWeights B i p, 0 < w := by
      intro w hw
      obtain ⟨m, _, rfl⟩ := List.mem_map.1 hw
      omega
    apply (mem_tuples hw).2
    refine ⟨by simp [vector,modeWeights], ?_⟩
    change weightSum (modeWeights B i p) ((modes B i p).map (encode x)) < p
    rw [modeWeights, weightSum_map, modes, ← Multiset.sum_coe, ← Multiset.map_coe,
      Finset.coe_toList]
    change (∑ m : Mode B i p, (m.2.2.val + 1) * encode x m) < p
    apply lt_of_le_of_lt _ (Nat.lt_of_not_ge hbudget)
    calc
      _ ≤ ∑ m : Mode B i p, if m ∈ small then k else 0 :=
        Finset.sum_le_sum fun m _ => bound x m
      _ = Fintype.card B * k * k := by
        rw [← Finset.sum_filter]
        have hs : (Finset.univ.filter fun m => m ∈ small) = small := by
          ext m
          simp
        rw [hs, Finset.sum_const, nsmul_eq_mul]
        simp only [small, Finset.card_map, Finset.card_univ, Fintype.card_prod,
          Fintype.card_fin]
        rfl
  have hj : Function.Injective vector := by
    intro x y h
    funext j
    have hh := (List.map_inj_left.mp h) (sm j) (by simp [modes])
    rw [encode_image, encode_image] at hh
    cases hx : x j <;> cases hy : y j <;> simp_all
  let dst := (tuples (modeWeights B i p) p).toFinset
  have hc := Fintype.card_le_of_injective
    (fun x => (⟨vector x, List.mem_toFinset.2 (hv x)⟩ : dst))
    (fun x y h => hj (congrArg Subtype.val h))
  have hcard : Fintype.card (B × Fin k → Bool) = 2 ^ (Fintype.card B * k) := by simp
  rw [hcard, Fintype.card_coe] at hc
  exact hc.trans (List.toFinset_card_le _)

theorem small_modes_lower {B : Type*} [Fintype B] {i p k : ℕ}
    (hk : k ≤ p - 1) (hbudget : Fintype.card B * k * k < p) :
    2 ^ (Fintype.card B * k) ≤ (tuples (modeWeights B i p) p).length :=
  (modeMask_le hk).resolve_right (Nat.not_le_of_lt hbudget)

def lowWeights (u L : ℕ) : ℕ := L / (Nat.sqrt u + 1)

theorem lowWeights_budget {u L M B : ℕ} (hM : 0 < M) (hL : 0 < L)
    (hB : B * L ≤ 3 * M) (hcover : M ≤ 2 * (B * L)) {p : ℕ} (hp : 24 * M * L ≤ u * p) :
    lowWeights u L ≤ p - 1 ∧ B * lowWeights u L * lowWeights u L < p := by
  let k := lowWeights u L
  let q := Nat.sqrt u + 1
  have hq : u < q * q := Nat.lt_succ_sqrt u
  have hk : k * q ≤ L := Nat.div_mul_le_self _ _
  have hsq : (q*q) * (k*k) ≤ L * L := by
    calc
      _ = (k*q)*(k*q) := by ring
      _ ≤ _ := Nat.mul_le_mul hk hk
  have aux : (u * (B*k*k)) * L ≤ (3*M*L) * L := by
    calc
      _ = (B*L) * (u*(k*k)) := by ring
      _ ≤ (3*M) * ((q*q)*(k*k)) :=
        Nat.mul_le_mul hB (Nat.mul_le_mul_right (k*k) hq.le)
      _ ≤ (3*M) * (L*L) := Nat.mul_le_mul_left _ hsq
      _ = _ := by ring
  have hx : u * (B*k*k) ≤ 3*M*L := Nat.le_of_mul_le_mul_right aux hL
  have hy : 3*M*L < 24*M*L := by
    have := Nat.mul_pos hM hL
    have h3 : 3*M*L = 3*(M*L) := by ring
    have h24 : 24*M*L = 24*(M*L) := by ring
    omega
  have hz : B*k*k < p := Nat.lt_of_mul_lt_mul_left (hx.trans_lt (hy.trans_le hp))
  have hBZ : 0 < B := by by_contra! h; simp [Nat.eq_zero_of_le_zero h] at hcover; omega
  have hk' : k ≤ B*k*k ∨ k = 0 := by
    by_cases h : k = 0
    · exact Or.inr h
    left
    have h1 : 1 ≤ B*k := Nat.mul_pos hBZ (Nat.pos_of_ne_zero h)
    simpa using Nat.mul_le_mul_right k h1
  exact ⟨by omega, hz⟩

theorem lowWeights_exponent {u L M B : ℕ} (hcover : M ≤ 2 * (B * L))
    (hL : 2 * (Nat.sqrt u + 1) ≤ L) :
    M ≤ 4 * (Nat.sqrt u + 1) * (B * lowWeights u L) := by
  let q := Nat.sqrt u + 1
  let k := lowWeights u L
  have hq : 0 < q := by simp [q]
  have hk : L = L % q + q*k := (Nat.mod_add_div L q).symm
  have hr := Nat.mod_lt L hq
  have hqk : q ≤ q*k := by omega
  have hl : L ≤ 2*(q*k) := by omega
  calc
    M ≤ 2 * (B*L) := hcover
    _ ≤ 2 * (B*(2*(q*k))) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hl)
    _ = _ := by unfold q k; ring

#print axioms Packing.mixed_capacity
#print axioms Packing.mixed_upper
#print axioms small_modes_lower
#print axioms lowWeights_budget
#print axioms lowWeights_exponent

end S11

