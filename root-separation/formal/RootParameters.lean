import RootEntry

/-! Appendix D 76–111, specialized to the root, with integer rounding. -/

namespace RootSeparation

open Entry S11

private theorem degree_exists (s : ℕ) : ∃ d : ℕ, s^9 ≤ d^10 := by
  refine ⟨s, ?_⟩
  cases s with
  | zero => decide
  | succ s => exact Nat.pow_le_pow_right (by omega) (by decide)

def degreeEnvelope (s : ℕ) : ℕ := Nat.find (degree_exists s)

theorem degree_valid (s : ℕ) : s^9 ≤ degreeEnvelope s ^ 10 := Nat.find_spec (degree_exists s)

theorem degree_le {s d : ℕ} (h : s^9 ≤ d^10) : degreeEnvelope s ≤ d := Nat.find_min' _ h

def fullCells (s : ℕ) : ℕ := 64 ^ (2 * labelLength s 0)

private theorem twoPowMono {x y : ℕ} (h : x ≤ y) : (2 : ℕ)^x ≤ 2^y :=
  Nat.pow_le_pow_right (by decide) h

private theorem root_powers (s : ℕ) :
    let a := labelLength s 0
    let L := packetLength s 0
    let Q := fullCells s
    L = 2^a ∧ Q = 2^(12*a) ∧ L*Q = 2^(13*a) ∧ 2*Q^2 = 2^(24*a+1) := by
  dsimp [packetLength, fullCells]
  have hQ : (64 : ℕ) ^ (2 * labelLength s 0) = 2 ^ (12 * labelLength s 0) := by
    rw [show (64 : ℕ) = 2^6 by decide, ← pow_mul]
    congr 1
    omega
  rw [hQ, ← pow_add, ← pow_mul]
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · congr 1
    omega
  · calc
      2 * 2 ^ (12 * labelLength s 0 * 2) = 2^(1+(12 * labelLength s 0 * 2)) := by rw [pow_add]; rfl
      _ = _ := by congr 1; omega

/-- All root packing inequalities and enough probe residues, using
s ≤ M ≤ 3s as holds on the uncloned branch. -/
theorem root_numeric {s M : ℕ} (hlambda : 131072 ≤ lambda s)
    (hsM : s ≤ M) (hMs : M ≤ 3*s) :
    let u := retained s 0
    let a := labelLength s 0
    let L := packetLength s 0
    let Q := fullCells s
    let Δ := degreeEnvelope s
    0 < u ∧ u ≤ M ∧ 1 < L ∧ 3 ≤ Δ ∧
    2*Q^2*Δ ≤ M ∧ L*Q ≤ M ∧ 2*L ≤ Δ ∧
    probeCount M L ≤ 2^(4*lambda s) := by
  intro u a L Q Δ
  let l := lambda s
  have hl : 131072 ≤ l := hlambda
  have ha : a = 2*u := (root_parameters s).1
  have hu : u = l / 131072 := by simp [u, retained, l]
  have hmul : 131072*u ≤ l := by rw [hu]; exact Nat.mul_div_le _ _
  have hupos : 0 < u := by omega
  have hlogHi : s ≤ 2^l := (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).1 le_rfl
  have hlogLo : 2^(l-1) < s :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).1 (by change l - 1 < l; omega)
  obtain ⟨hL,hQ,hLQ,hQQ⟩ := root_powers s
  change L = 2^a at hL
  change Q = 2^(12*a) at hQ
  change L*Q = 2^(13*a) at hLQ
  change 2*Q^2 = 2^(24*a+1) at hQQ
  let b := (9*l+9)/10
  have hb : 9*l ≤ 10*b := by dsimp [b]; omega
  have hΔup : Δ ≤ 2^b := by
    apply degree_le
    calc
      s^9 ≤ (2^l)^9 := Nat.pow_le_pow_left hlogHi _
      _ ≤ (2^b)^10 := by rw [← pow_mul, ← pow_mul]; apply twoPowMono; omega
  have hlow : 2^(a+1) ≤ Δ := by
    apply le_of_not_gt
    intro h
    have hbad : Δ^10 < (2^(a+1))^10 :=
      Nat.pow_lt_pow_left h (by decide)
    have hp : (2^(a+1))^10 ≤ (2^(l-1))^9 := by
      rw [← pow_mul, ← pow_mul]
      apply twoPowMono
      omega
    have hs := Nat.pow_le_pow_left hlogLo.le 9
    exact (not_lt_of_ge ((hp.trans hs).trans (degree_valid s))) hbad
  have h2L : 2*L ≤ Δ := by rw [hL]; simpa [pow_succ, Nat.mul_comm] using hlow
  have hbig : 2*Q^2*Δ ≤ M := by
    rw [hQQ]
    calc
      _ ≤ 2^(24*a+1) * 2^b := Nat.mul_le_mul_left _ hΔup
      _ ≤ 2^(l-1) := by
        rw [← pow_add]
        apply twoPowMono
        dsimp [b]
        omega
      _ ≤ M := hlogLo.le.trans hsM
  have hslots : L*Q ≤ M := by
    rw [hLQ]
    exact (twoPowMono (show 13*a ≤ l-1 by omega)).trans (hlogLo.le.trans hsM)
  have hLgt : 1 < L := by rw [hL]; exact Nat.one_lt_two_pow (by omega)
  have hsmall : u ≤ M := by
    have hlo : l - 1 < 2^(l-1) := Nat.lt_two_pow_self
    omega
  refine ⟨hupos,hsmall,hLgt,by omega,hbig,hslots,h2L,?_⟩
  have hm : M ≤ 2^(l+2) := by
    calc
      _ ≤ 3 * s := hMs
      _ ≤ 4 * 2^l := by omega
      _ = _ := by rw [pow_add]; ring
  have hp : M * (2*L-1) ≤ 2^(l+2) * 2^(a+1) := by
    apply Nat.mul_le_mul hm
    rw [hL, pow_succ]
    omega
  rw [← pow_add] at hp
  have hpow := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ))
    (show l+2+(a+1) < 4*l by omega)
  change M * (2*L-1) + 1 ≤ 2^(4*l)
  omega

theorem cell_count (s : ℕ) :
    Fintype.card ((Fin (labelLength s 0) → Fin 64) × (Fin (labelLength s 0) → Fin 64)) =
      fullCells s := by
  rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_add]
  unfold fullCells
  congr 1
  omega

theorem root_scale {s : ℕ} (hlambda : 131072 ≤ lambda s) :
    packetLength s 0 ^ 1000 ≤ s ∧ fullCells s ^ 1000 ≤ s := by
  let l := lambda s
  let a := labelLength s 0
  let u := retained s 0
  have ha : a = 2*u := (root_parameters s).1
  have hu : u = l / 131072 := by simp [u, retained, l]
  have hmul : 131072*u ≤ l := by rw [hu]; exact Nat.mul_div_le _ _
  have hlogLo : 2^(l-1) < s :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).1 (by change l-1 < l; omega)
  have h1 : a * 1000 ≤ l-1 := by omega
  have h2 : (12*a) * 1000 ≤ l-1 := by omega
  obtain ⟨hL,hQ,_,_⟩ := root_powers s
  constructor
  · rw [hL, ← pow_mul]
    exact (twoPowMono h1).trans hlogLo.le
  · rw [hQ, ← pow_mul]
    exact (twoPowMono h2).trans hlogLo.le

#print axioms root_scale
#print axioms root_numeric
#print axioms cell_count

end RootSeparation
