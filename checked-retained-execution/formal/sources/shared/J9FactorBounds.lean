import NativeBitBudget
import CompletedPrecisionBudget
import J9PrintedSchedule
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

namespace J9FactorBounds
open scoped BigOperators

/-- Literal outer-center scalar c=C'(L-1)/C'(0) from the source. -/
def kernel (L : ℕ) : ℤ := -(((2*L-1).choose L : ℕ) : ℤ)

theorem kernel_nonpos (L : ℕ) : kernel L ≤ 0 := by
  unfold kernel
  exact neg_nonpos.mpr (by positivity)

/-- The source binomial gives the exact uniform elementary kernel budget. -/
theorem kernel_budget (L : ℕ) (hL : 1 ≤ L) : 1 + |kernel L| ≤ (2:ℤ)^(2*L) := by
  have hb : (((2*L-1).choose L : ℕ) : ℤ) ≤ (2:ℤ)^(2*L-1) := by
    exact_mod_cast Nat.choose_le_two_pow (2*L-1) L
  have hp : (1:ℤ) ≤ (2:ℤ)^(2*L-1) := one_le_pow₀ (by decide)
  have he : (2*L-1)+1 = 2*L := by omega
  calc
    1+|kernel L| = 1+(((2*L-1).choose L : ℕ) : ℤ) := by simp [kernel]
    _ ≤ 1+(2:ℤ)^(2*L-1) := add_le_add_left hb _
    _ ≤ (2:ℤ)^(2*L-1)*2 := by omega
    _ = (2:ℤ)^(2*L) := by rw [← pow_succ, he]

/-- Multilinear extension of the binary subdivision equality. -/
def equalityPoly (u v : ℤ) : ℤ := 1-u-v+2*u*v

/-- The argument at zero is the coefficient at an actual shifted port
if its column bit is true, and is zero otherwise. -/
def arg (c : ℤ) (hit bit : Bool) : ℤ := if hit && bit then c else 0

def rowBase (c : ℤ) (hit bits : Bool → Bool) : ℤ :=
  equalityPoly (arg c (hit false) (bits false)) (arg c (hit true) (bits true))

/-- The native one-leg difference; the original argument of the other leg
is retained, and the selected leg is evaluated at one and at zero. -/
def rowDiff (c : ℤ) (hit bits : Bool → Bool) (leg : Bool) : ℤ :=
  if leg then
    equalityPoly (arg c (hit false) (bits false)) 1 -
      equalityPoly (arg c (hit false) (bits false)) 0
  else
    equalityPoly 1 (arg c (hit true) (bits true)) -
      equalityPoly 0 (arg c (hit true) (bits true))

theorem rowDiff_formula (c : ℤ) (hit bits : Bool → Bool) (leg : Bool) :
    rowDiff c hit bits leg = -1+2*arg c (hit (!leg)) (bits (!leg)) := by
  cases leg <;> simp [rowDiff, equalityPoly] <;> ring

theorem rowDiff_abs_le (c : ℤ) (hc : c ≤ 0) (hit bits : Bool → Bool) (leg : Bool) :
    |rowDiff c hit bits leg| ≤ 2*(1+|c|) := by
  rw [rowDiff_formula, abs_of_nonpos hc]
  unfold arg
  split <;> rename_i h
  · rw [abs_of_nonpos (by omega)]
    omega
  · norm_num
    omega

/-- Endpoint-match sparsity reduces every actual binary baseline to 1
or a unary factor 1-c. -/
theorem rowBase_cases (c : ℤ) (hit bits : Bool → Bool)
    (hOne : ¬ (hit false = true ∧ hit true = true)) :
    rowBase c hit bits = 1 ∨ rowBase c hit bits = 1-c := by
  cases h0 : hit false <;> cases h1 : hit true <;>
    cases b0 : bits false <;> cases b1 : bits true <;>
    simp_all [rowBase, arg, equalityPoly]

theorem rowBase_abs_le (c : ℤ) (hc : c ≤ 0) (hit bits : Bool → Bool)
    (hOne : ¬ (hit false = true ∧ hit true = true)) :
    |rowBase c hit bits| ≤ 1+|c| := by
  rcases rowBase_cases c hit bits hOne with h | h
  · rw [h, abs_of_nonpos hc]
    norm_num
    omega
  · rw [h, abs_of_nonpos hc, abs_of_nonneg (by omega)]
    omega

structure Chart (L M : ℕ) (R T : Type*) where
  hit : R → Bool → Bool
  rowInput : R → Bool → Fin M
  table : (Fin M → Bool) → Bool
  tileSlot : T → Fin L
  tileInput : T → Fin M
  rowOf : Fin L → R
  leg : Fin L → Bool
  targets : Finset (Fin L)
  tau : Fin 2

variable {L M : ℕ} {R T : Type*} [Fintype R] [DecidableEq R] [Fintype T]

def activeRows (g : Chart L M R T) : Finset R :=
  Finset.univ.filter fun r => (g.hit r false || g.hit r true) = true

/-- The actual tile coordinate j=(slot-tau)/2, and the source moment
with bits read from the complete Boolean column assignment. -/
def moment (g : Chart L M R T) (b : ℕ) (x : Fin M → Bool) : ℤ :=
  (NativeBitBudget.tileMoment (fun t => ((g.tileSlot t).val-g.tau.val)/2)
    (fun t => x (g.tileInput t)) b : ℕ)

def difference (g : Chart L M R T) (i : Fin L) (x : Fin M → Bool) : ℤ :=
  rowDiff (kernel L) (g.hit (g.rowOf i)) (fun leg => x (g.rowInput (g.rowOf i) leg)) (g.leg i)

def baseline (g : Chart L M R T) (i : Fin L) (x : Fin M → Bool) : ℤ :=
  (if g.table x then 1 else 0) *
    ∏ r ∈ ((Finset.univ : Finset R).erase (g.rowOf i)),
      rowBase (kernel L) (g.hit r) (fun leg => x (g.rowInput r leg))

omit [Fintype R] [DecidableEq R] in
theorem moment_abs_le (g : Chart L M R T) (b : ℕ) (x : Fin M → Bool)
    (hL : 3 ≤ L) (hTile : Function.Injective g.tileSlot) :
    |moment g b x| ≤ (2:ℤ)^((b+1)*L) := by
  have hc : Fintype.card T ≤ L := by
    simpa using Fintype.card_le_of_injective g.tileSlot hTile
  have hd : ∀ t : T, ((g.tileSlot t).val-g.tau.val)/2 ≤ L := by
    intro t
    exact ((Nat.div_le_self _ _).trans (Nat.sub_le _ _)).trans (g.tileSlot t).isLt.le
  have ht := NativeBitBudget.tileMoment_le
    (fun t => ((g.tileSlot t).val-g.tau.val)/2) (fun t => x (g.tileInput t)) b L hc hd
  have hL' : L ≤ 2^L := by
    have hh := CompletedPrecisionBudget.twice_le_pow L (by omega)
    omega
  have hp : L^(b+1) ≤ (2:ℕ)^((b+1)*L) := by
    calc
      _ ≤ (2^L)^(b+1) := Nat.pow_le_pow_left hL' _
      _ = _ := by rw [← Nat.pow_mul, Nat.mul_comm L (b+1)]
  unfold moment
  rw [abs_of_nonneg (by positivity)]
  exact_mod_cast ht.trans hp

omit [Fintype R] [DecidableEq R] [Fintype T] in
theorem difference_abs_le (g : Chart L M R T) (i : Fin L) (x : Fin M → Bool)
    (hL : 1 ≤ L) : |difference g i x| ≤ (2:ℤ)^(2*L+1) := by
  unfold difference
  calc
    _ ≤ 2*(1+|kernel L|) := rowDiff_abs_le _ (kernel_nonpos _) _ _ _
    _ ≤ 2*(2:ℤ)^(2*L) := mul_le_mul_of_nonneg_left (kernel_budget L hL) (by decide)
    _ = _ := (pow_succ' _ _).symm

omit [Fintype T] in
theorem baseline_abs_le (g : Chart L M R T) (i : Fin L) (x : Fin M → Bool) (hL : 1 ≤ L)
    (hOne : ∀ r, ¬ (g.hit r false = true ∧ g.hit r true = true)) :
    |baseline g i x| ≤ (2:ℤ)^(2*L*(activeRows g).card) := by
  let base : R → ℤ := fun r =>
    rowBase (kernel L) (g.hit r) (fun leg => x (g.rowInput r leg))
  let rows : Finset R := (Finset.univ : Finset R).erase (g.rowOf i)
  let kept := rows.filter fun r => (g.hit r false || g.hit r true) = true
  have hsub : kept ⊆ activeRows g := by
    intro r hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hr).2⟩
  have he : (∏ r ∈ rows, base r) = ∏ r ∈ kept, base r := by
    dsimp [kept]
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro r hr
    by_cases h : (g.hit r false || g.hit r true) = true
    · simp [h]
    · cases h0 : g.hit r false <;> cases h1 : g.hit r true <;>
        simp_all [base, rowBase, equalityPoly, arg]
  have hB : |∏ r ∈ kept, base r| ≤ (2:ℤ)^(2*L*(activeRows g).card) := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _r ∈ kept, (2:ℤ)^(2*L) := by
        apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        intro r hr
        exact (rowBase_abs_le _ (kernel_nonpos _) _ _ (hOne r)).trans (kernel_budget L hL)
      _ = (2:ℤ)^(2*L*kept.card) := by
        rw [Finset.prod_const]
        exact (pow_mul (2:ℤ) (2*L) kept.card).symm
      _ ≤ _ := pow_le_pow_right₀ (by decide)
        (Nat.mul_le_mul_left _ (Finset.card_le_card hsub))
  change |(if g.table x then (1:ℤ) else 0) * ∏ r ∈ rows, base r| ≤ _
  rw [he]
  cases hp : g.table x
  · simp only [Bool.false_eq_true, if_false, zero_mul, abs_zero]
    positivity
  · simpa [hp] using hB

def denominator (g : Chart L M R T) (b : ℕ) (i : Fin L) : ℤ :=
  ((L:ℤ)-1-(g.tau.val:ℤ)+(i.val:ℤ))^(b+1)

def slope (L b : ℕ) : ℤ := kernel L * (2*(L:ℤ)) * 2^b

def term (g : Chart L M R T) (b : ℕ) (i : Fin L) (x : Fin M → Bool) : ℤ :=
  moment g b x * difference g i x * baseline g i x

noncomputable def exactCleared (g : Chart L M R T) (b : ℕ) : ℤ := by
  classical
  exact CompletedPrecisionBudget.cleared g.targets Finset.univ
    (denominator g b) (fun _ => slope L b) (term g b)

noncomputable def firstCoeff (g : Chart L M R T) (b : ℕ) : ℚ := by
  classical
  exact ∑ i ∈ g.targets,
    ((slope L b * (∑ x : Fin M → Bool, term g b i x) : ℤ) : ℚ) / denominator g b i

def publicDenominator (g : Chart L M R T) (b : ℕ) : ℤ :=
  ∏ i ∈ g.targets, denominator g b i

omit [Fintype R] [DecidableEq R] [Fintype T] in
theorem local_den_positive_odd (g : Chart L M R T) (b : ℕ) (hL : 3 ≤ L)
    (hEven : L % 2 = 0) (hpar : ∀ i ∈ g.targets, i.val%2=g.tau.val%2)
    (i : Fin L) (hi : i ∈ g.targets) :
    0 < denominator g b i ∧ Odd (denominator g b i) := by
  have h := CompletedPrecisionBudget.outer_denominator L i.val g.tau.val hL
    i.isLt g.tau.isLt hEven (hpar i hi)
  exact ⟨pow_pos h.1 _, h.2.2.pow⟩

/-- The actual odd product clears every term in the first coefficient. -/
theorem cleared_exact_odd (g : Chart L M R T) (b : ℕ) (hL : 3 ≤ L)
    (hEven : L % 2 = 0) (hpar : ∀ i ∈ g.targets, i.val%2=g.tau.val%2) :
    Odd (publicDenominator g b) ∧
      (exactCleared g b : ℚ) = (publicDenominator g b : ℚ) * firstCoeff g b := by
  classical
  refine ⟨CoefficientClearing.product_odd _ _ (fun i hi =>
    (local_den_positive_odd g b hL hEven hpar i hi).2), ?_⟩
  exact CompletedPrecisionBudget.cleared_correct g.targets Finset.univ
    (denominator g b) (fun _ => slope L b) (term g b)
    (fun i hi => (local_den_positive_odd g b hL hEven hpar i hi).1.ne')

/-- J9 with literal factor functions. Only finite geometry and parameter
bounds remain as hypotheses, not any bounds on the four separate factors. -/
theorem actual_factors_centered (g : Chart L M R T) (b : ℕ) (hL : 3 ≤ L)
    (hEven : L % 2 = 0) (hb : b < L) (hCube : L^3 ≤ M)
    (hpar : ∀ i ∈ g.targets, i.val%2=g.tau.val%2)
    (hTile : Function.Injective g.tileSlot)
    (hOne : ∀ r, ¬ (g.hit r false = true ∧ g.hit r true = true))
    (hCount : L * (activeRows g).card ≤ 3*M) :
    (exactCleared g b)*2 ∈ Set.Ioc (-(2:ℤ)^(10*M)) ((2:ℤ)^(10*M)) := by
  classical
  have hs : g.targets.card ≤ L := by
    simpa using (Finset.card_le_univ g.targets)
  have ha : (Finset.univ : Finset (Fin M → Bool)).card ≤ 2^M := by
    simp
  have hc : |kernel L| ≤ (2:ℤ)^(2*L) := by
    have h := kernel_budget L (by omega)
    omega
  exact CompletedPrecisionBudget.outer_centered
    g.targets g.targets Finset.univ (fun i => i.val) g.tau.val (kernel L)
    (fun _ x => moment g b x) (difference g) (baseline g)
    L b M (activeRows g).card hL hEven g.tau.isLt hb hCube
    hs ha hCount (Finset.Subset.rfl)
    (fun i hi => ⟨i.isLt, hpar i hi⟩) hc
    (fun _ _ x _ => moment_abs_le g b x hL hTile)
    (fun i _ x _ => difference_abs_le g i x (by omega))
    (fun i _ x _ => baseline_abs_le g i x (by omega) hOne)


/-- Choose the positive representative in the half-way tie. This is exactly
the (-m/2,m/2] convention of the finite coefficient budget theorem. -/
def centerResidue (modulus a : ℤ) : ℤ :=
  let r := a % modulus
  if 2*r ≤ modulus then r else r-modulus

theorem centerResidue_range (modulus a : ℤ) (hm : 0 < modulus) :
    centerResidue modulus a * 2 ∈ Set.Ioc (-modulus) modulus := by
  have hlo := Int.emod_nonneg a hm.ne'
  have hhi := Int.emod_lt_of_pos a hm
  unfold centerResidue
  dsimp only
  split <;> constructor <;> omega

theorem centerResidue_congr (modulus a : ℤ) :
    modulus ∣ centerResidue modulus a - a := by
  have h := Int.emod_add_mul_ediv a modulus
  unfold centerResidue
  dsimp only
  split
  · refine ⟨-(a/modulus), ?_⟩
    nlinarith
  · refine ⟨-(a/modulus)-1, ?_⟩
    nlinarith

theorem centerResidue_unique {modulus a z : ℤ} (hm : 0 < modulus)
    (hz : z*2 ∈ Set.Ioc (-modulus) modulus) (hRes : modulus ∣ a-z) :
    centerResidue modulus a = z := by
  let y := centerResidue modulus a
  have hy : y*2 ∈ Set.Ioc (-modulus) modulus := centerResidue_range modulus a hm
  have hh : |y-z| < modulus := by
    rw [abs_lt]
    exact ⟨by have := hy.1; have := hz.2; omega,
           by have := hy.2; have := hz.1; omega⟩
  have hDiv : modulus ∣ y-z := by
    have h := dvd_add (centerResidue_congr modulus a) hRes
    have he : y-z = (y-a)+(a-z) := by ring
    exact he ▸ h
  obtain ⟨k,hk⟩ := hDiv
  by_contra hn
  have hkn : k ≠ 0 := by
    intro h0
    apply hn
    rw [h0, mul_zero] at hk
    exact sub_eq_zero.mp hk
  have hk' : (1:ℤ) ≤ |k| := by
    have hu := abs_pos.mpr hkn
    omega
  rw [hk, abs_mul, abs_of_pos hm] at hh
  nlinarith

/-- Finite J9 numerical certificate at the native odd outer root. There are
no input inequalities for individual magnitudes of moment, baseline,
difference, slope or denominator. The certified matching and the parity of
target rows are explicit geometric hypotheses. A reduced residue is
assumed to be the residue of the already denominator-cleared coefficient. -/
theorem printed_center_recover (s M p b : ℕ)
    (g : Chart (J9PrintedSchedule.rootL (Nat.clog 2 s)) M R T)
    (hLambda : 262144 ≤ Nat.clog 2 s)
    (hActive : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M)
    (hP : 0 < p)
    (hb : b < J9PrintedSchedule.rootL (Nat.clog 2 s))
    (hpar : ∀ i ∈ g.targets, i.val%2=g.tau.val%2)
    (hTile : Function.Injective g.tileSlot)
    (hOne : ∀ r, ¬ (g.hit r false = true ∧ g.hit r true = true))
    (hCount : J9PrintedSchedule.rootL (Nat.clog 2 s) * (activeRows g).card ≤ 3*M) :
    let lambda := Nat.clog 2 s
    let L := J9PrintedSchedule.rootL lambda
    let u := J9PrintedSchedule.rootU lambda
    let a := J9PrintedSchedule.rootA lambda
    let pt := J9PrintedSchedule.precision p ((3*M+u-1)/u) L M a
    let modulus := (2:ℤ)^(10*M)
    10*M < pt ∧ 10*M+1 ≤ J9PrintedSchedule.probeCount M L ∧
      Odd (publicDenominator g b) ∧
      (exactCleared g b)*2 ∈ Set.Ioc (-modulus) modulus ∧
      ∀ z : ℤ, modulus ∣ z - exactCleared g b →
        centerResidue modulus z = exactCleared g b ∧
        ((centerResidue modulus z : ℤ) : ℚ) / publicDenominator g b = firstCoeff g b := by
  classical
  let lambda := Nat.clog 2 s
  let len := J9PrintedSchedule.rootL lambda
  let modulus := (2:ℤ)^(10*M)
  have hL : 6 ≤ len := (J9PrintedSchedule.rootL_ge_six_iff_lambda lambda).2 hLambda
  have hu₂ : 2 ≤ J9PrintedSchedule.rootU lambda :=
    (J9PrintedSchedule.rootL_ge_six_iff_u lambda).1 hL
  have hu₁ : 1 ≤ J9PrintedSchedule.rootU lambda := by omega
  have hA : 1 ≤ J9PrintedSchedule.rootA lambda := by unfold J9PrintedSchedule.rootA; omega
  have hOdd := J9PrintedSchedule.root_outer_odd lambda hu₁
  have hEven : len%2=0 := by change (len-1)%2=1 at hOdd; omega
  have hSmall : 3 ≤ len := by omega
  have hCube : len^3 ≤ M := J9PrintedSchedule.root_cube_le_active_M s M hActive
  have hRange := actual_factors_centered g b hSmall hEven hb hCube hpar hTile hOne hCount
  have hClear := cleared_exact_odd g b hSmall hEven hpar
  have hd : 0 < publicDenominator g b :=
    Finset.prod_pos (fun i hi => (local_den_positive_odd g b hSmall hEven hpar i hi).1)
  have hd' : (publicDenominator g b : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  refine ⟨J9PrintedSchedule.precision_gt_ten _ _ _ _ _ hP hA,
    J9PrintedSchedule.probes_ge_ten_add_one _ _ hL, hClear.1, hRange, ?_⟩
  intro z hz
  have hm : 0 < modulus := by dsimp [modulus]; positivity
  have he := centerResidue_unique hm hRange hz
  refine ⟨he, ?_⟩
  rw [he, hClear.2]
  field_simp

#print axioms centerResidue_unique
#print axioms printed_center_recover
#print axioms kernel_budget
#print axioms rowDiff_formula
#print axioms rowBase_cases
#print axioms moment_abs_le
#print axioms baseline_abs_le
#print axioms cleared_exact_odd
#print axioms actual_factors_centered

end J9FactorBounds
