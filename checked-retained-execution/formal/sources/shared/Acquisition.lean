import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Exact algebraic core of the native acquisition reduction

The value considered here is the signed zero-mode root at the mesh shift `-1`,
after the Cauchy coefficients have specialized to the predecessor kernel.
The definitions retain independent physical row and column bits, the added
all-ones rows, and the added zero-pinned columns. These are identities for
one register, not lower bounds for producing the final origin answer.

The explicit legal layout is supplied, with its predecessor relation exposed;
this file does not formalize the uniform packing algorithm, its asymptotics,
the source schedule selection, or the external counting-completeness results.
-/

open scoped BigOperators

namespace Acquisition

section Algebra

variable {K : Type*} [CommRing K]

/-- Interpret a Boolean as a scalar without choosing a characteristic. -/
def bit (b : Bool) : K := if b then 1 else 0

/-- The two affine Lagrange functions of a Boolean port. -/
def lag : Bool → K → K
  | false, a => 1 - a
  | true, a => a

theorem lag_partition (a : K) : ∑ b : Bool, lag b a = 1 := by
  simp [lag]

theorem lag_first_moment (a : K) : ∑ b : Bool, bit b * lag b a = a := by
  simp [bit, lag]

/-- The multilinear extension, defined by a sum over all local row bits. -/
def extension {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → Bool) → K) (a : I → K) : K :=
  ∑ x : I → Bool, f x * ∏ i : I, lag (x i) (a i)

theorem extension_one {I : Type*} [Fintype I] [DecidableEq I] (a : I → K) :
    extension (fun _ => 1) a = 1 := by
  simp only [extension, one_mul]
  rw [← Fintype.prod_sum (fun i (b : Bool) => lag b (a i))]
  simp only [lag_partition, Finset.prod_const_one]

theorem extension_full_monomial {I : Type*} [Fintype I] [DecidableEq I] (a : I → K) :
    extension (fun y => ∏ i : I, bit (y i)) a = ∏ i : I, a i := by
  simp only [extension, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) => bit b * lag b (a i))]
  simp only [lag_first_moment]

theorem extension_negative_clause {I : Type*} [Fintype I] [DecidableEq I] (a : I → K) :
    extension (fun y => 1 - ∏ i : I, bit (y i)) a = 1 - ∏ i : I, a i := by
  simp only [extension, sub_mul, one_mul, Finset.sum_sub_distrib]
  have h₁ := extension_one a
  have h₂ := extension_full_monomial a
  simp only [extension, one_mul] at h₁ h₂
  rw [h₁, h₂]

/-- A standalone equal-bit tensor on the fibers of the given incidence map. -/
noncomputable def equalityTensor {I V : Type*} [Fintype V] (own : I → V) (X : I → Bool) : K := by
  classical
  exact ∏ v : V, if ∀ i j, own i = v → own j = v → X i = X j then 1 else 0

/-- Each equality column chooses its own bit. The surjectivity hypothesis says
that there is an actual port on every column; it holds for cubic graphs. -/
theorem equalityTensor_sum {I V : Type*} [Fintype I] [DecidableEq I]
    [Fintype V] [DecidableEq V] (own : I → V) (onto : Function.Surjective own)
    (f : (I → Bool) → K) :
    (∑ X : I → Bool, equalityTensor own X * f X) = ∑ x : V → Bool, f (x ∘ own) := by
  classical
  have consistent (X : I → Bool) :
      (∀ v i j, own i = v → own j = v → X i = X j) ↔ ∃ x : V → Bool, x ∘ own = X := by
    constructor
    · intro h
      let x : V → Bool := fun v => X ((onto v).choose)
      refine ⟨x, ?_⟩
      funext i
      exact h (own i) _ _ (onto (own i)).choose_spec rfl
    · rintro ⟨x, rfl⟩ v i j hi hj
      simp only [Function.comp_apply, hi, hj]
  have val (X : I → Bool) :
      equalityTensor (K := K) own X = if ∃ x : V → Bool, x ∘ own = X then 1 else 0 := by
    by_cases hex : ∃ x : V → Bool, x ∘ own = X
    · simp only [if_pos hex, equalityTensor]
      exact Finset.prod_eq_one fun v _ => if_pos ((consistent X).mpr hex v)
    · simp only [if_neg hex, equalityTensor]
      obtain ⟨v, hv⟩ := not_forall.mp (fun H => hex ((consistent X).mp H))
      exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)
  calc
    (∑ X, equalityTensor (K := K) own X * f X) =
        ∑ X ∈ (Finset.univ : Finset (I → Bool)).filter (fun X => ∃ x : V → Bool, x ∘ own = X), f X := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro X _
      by_cases h : ∃ x : V → Bool, x ∘ own = X
      · simp [val, h]
      · simp [val, h]
    _ = _ := ?_
  symm
  apply Finset.sum_bij (fun x _ => x ∘ own)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x, rfl⟩
  · intro x hx y hy he
    funext v
    obtain ⟨i, rfl⟩ := onto v
    exact congrFun he i
  · intro X hX
    obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hX).2
    exact ⟨x, Finset.mem_univ _, hx⟩
  · intros
    rfl

end Algebra

section Mesh

/-- The source interpolation mesh, as integers. -/
def mesh (L : ℕ) : Finset ℤ := Finset.Icc (-(L : ℤ)) ((L : ℤ) - 1)

/-- Polynomial quotient with its indicated linear factor deleted. If the
index is not in the mesh, this is the whole product. -/
def meshDeleted (L : ℕ) (q t : ℤ) : ℤ := ∏ j ∈ (mesh L).erase q, (t - j)

theorem meshDeleted_den_nonzero (L : ℕ) : meshDeleted L 0 0 ≠ 0 := by
  unfold meshDeleted
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  have hn := (Finset.mem_erase.mp hj).1
  omega

/-- Exact integer kernel specialization, before any division or modular
reduction. This also handles crossing factors with a deleted index outside
the mesh (erasing such an index leaves the full mesh product). -/
theorem meshDeleted_minus_one (L : ℕ) (hL : 0 < L) (q : ℤ) :
    meshDeleted L q (-1) =
      (if q = -1 then -1 else 0) * meshDeleted L 0 0 := by
  have h0 : (0 : ℤ) ∈ mesh L := by
    simp only [mesh, Finset.mem_Icc]
    omega
  have hm : (-1 : ℤ) ∈ mesh L := by
    simp only [mesh, Finset.mem_Icc]
    omega
  by_cases hq : q = -1
  · subst q
    simp only [if_true, meshDeleted]
    have reflected :
        (∏ j ∈ (mesh L).erase (-1), ((-1 : ℤ) - j)) =
          ∏ j ∈ (mesh L).erase 0, j := by
      apply Finset.prod_bij (fun j _ => -1 - j)
      · intro j hj
        simp only [mesh, Finset.mem_erase, Finset.mem_Icc] at hj ⊢
        omega
      · intros
        omega
      · intro j hj
        refine ⟨-1-j, ?_, by omega⟩
        simp only [mesh, Finset.mem_erase, Finset.mem_Icc] at hj ⊢
        omega
      · intros
        rfl
    have card : ((mesh L).erase 0).card = 2 * (L-1) + 1 := by
      rw [Finset.card_erase_of_mem h0, mesh, Int.card_Icc]
      omega
    have sign : (-1 : ℤ) ^ ((mesh L).erase 0).card = -1 := by
      rw [card, pow_add, pow_mul]
      norm_num
    have negprod :
        (∏ j ∈ (mesh L).erase 0, ((0 : ℤ) - j)) =
          - (∏ j ∈ (mesh L).erase 0, j) := by
      have h : (fun j : ℤ => (0 : ℤ) - j) = fun j => (-1 : ℤ) * j := by
        funext j
        ring
      rw [h, Finset.prod_mul_distrib, Finset.prod_const, sign, neg_one_mul]
    rw [reflected, negprod]
    ring
  · rw [if_neg hq, zero_mul]
    apply Finset.prod_eq_zero (i := (-1 : ℤ))
    · exact Finset.mem_erase.mpr ⟨Ne.symm hq, hm⟩
    · ring

/-- The associated rational local Cauchy coefficient is precisely the signed
predecessor: -1 there and zero at every other offset. -/
theorem cauchy_minus_one (L : ℕ) (hL : 0 < L) (q : ℤ) :
    (meshDeleted L q (-1) : ℚ) / (meshDeleted L 0 0 : ℚ) =
      if q = -1 then -1 else 0 := by
  rw [meshDeleted_minus_one L hL]
  by_cases hq : q = -1 <;> simp only [hq, if_true, if_false, Int.cast_mul,
    Int.cast_neg, Int.cast_one, Int.cast_zero, zero_mul, zero_div]
  have hden : (meshDeleted L 0 0 : ℚ) ≠ 0 := by
    exact_mod_cast meshDeleted_den_nonzero L
  rw [mul_div_assoc, div_self hden, mul_one]

end Mesh


section Paired

variable {K : Type*} [CommRing K]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The collection of odd physical columns, each separately pinned to zero. -/
def pinsZero (B : I → Bool) : K := ∏ i : I, (if B i = false then 1 else 0)

omit [DecidableEq I] in
theorem pinsZero_eq (B : I → Bool) :
    pinsZero (K := K) B = if B = (fun _ => false) then 1 else 0 := by
  rw [pinsZero, Finset.prod_boole]
  simp only [Finset.mem_univ, true_implies, funext_iff]

/-- Two physical wires per incidence (even/odd). The even row is unary
all-ones, the odd column is unary zero-pinned. All row and column port bits
are independently summed. The odd row's source is the prescribed even
column. The even dummy row may have an odd predecessor or no predecessor. -/
def pairedRegister (row col : (I → Bool) → K) (earlier : I → Option I) : K :=
  ∑ X : (I → Bool) × (I → Bool), ∑ Y : (I → Bool) × (I → Bool),
    (col X.1 * pinsZero X.2) *
      ((row Y.2 * (∏ i : I, lag (Y.2 i) (-bit (X.1 i)))) *
        (∏ i : I, lag (Y.1 i) (-bit (((earlier i).map X.2).getD false))))

theorem pairedRegister_collapse (row col : (I → Bool) → K) (earlier : I → Option I) :
    pairedRegister row col earlier =
      ∑ x : I → Bool, col x * extension row (fun i => -bit (x i)) := by
  classical
  rw [pairedRegister, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  have inner (t : I → Bool) :
      (∑ Y : (I → Bool) × (I → Bool),
        (col x * pinsZero t) *
          ((row Y.2 * (∏ i : I, lag (Y.2 i) (-bit (x i)))) *
            (∏ i : I, lag (Y.1 i) (-bit (((earlier i).map t).getD false))))) =
        (col x * pinsZero t) * extension row (fun i => -bit (x i)) := by
    let a : I → K := fun i => -bit (((earlier i).map t).getD false)
    let f : (I → Bool) → K := fun v => row v * ∏ i : I, lag (v i) (-bit (x i))
    let g : (I → Bool) → K := fun u => ∏ i : I, lag (u i) (a i)
    change (∑ Y : (I → Bool) × (I → Bool), (col x * pinsZero t) * (f Y.2 * g Y.1)) = _
    rw [← Finset.mul_sum, Fintype.sum_prod_type]
    congr 1
    have h (u : I → Bool) : (∑ v : I → Bool, f v * g u) = g u * ∑ v : I → Bool, f v := by
      rw [← Finset.sum_mul, mul_comm]
    simp only [h, ← Finset.sum_mul]
    have hg : (∑ u : I → Bool, g u) = 1 := by
      simpa only [extension, one_mul] using
        (extension_one a : extension (fun _ => (1 : K)) a = 1)
    rw [hg, one_mul]
    rfl
  simp_rw [inner]
  simp only [pinsZero_eq, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Fintype.sum_ite_eq']

end Paired

section Rows

variable {K : Type*} [CommRing K]

/-- Original row tensors are independent across their port fibers. -/
def rowProduct {R : Type*} [Fintype R] {J : R → Type*}
    (f : (r : R) → (J r → Bool) → K) (Y : (Σ r, J r) → Bool) : K :=
  ∏ r : R, f r (fun j => Y ⟨r,j⟩)

theorem extension_rowProduct {R : Type*} [Fintype R] [DecidableEq R] {J : R → Type*}
    [(r : R) → Fintype (J r)] [(r : R) → DecidableEq (J r)]
    (f : (r : R) → (J r → Bool) → K) (a : (Σ r, J r) → K) :
    extension (rowProduct f) a = ∏ r : R, extension (f r) (fun j => a ⟨r,j⟩) := by
  classical
  simp only [extension]
  rw [Fintype.prod_sum (fun r (y : J r → Bool) => f r y * ∏ j : J r, lag (y j) (a ⟨r,j⟩))]
  apply Fintype.sum_equiv (Equiv.piCurry fun _ _ => Bool)
  intro y
  simp only [rowProduct, Equiv.piCurry_apply]
  have split :
      (∏ i : Σ r, J r, lag (y i) (a i)) =
        ∏ r : R, ∏ j : J r, lag (y ⟨r,j⟩) (a ⟨r,j⟩) := by
    simpa using (Finset.prod_sigma (Finset.univ : Finset R)
      (fun r => (Finset.univ : Finset (J r))) (fun i => lag (y i) (a i)))
  rw [split, Finset.prod_mul_distrib]
  rfl

/-- NAND is the all-negative two-port clause. -/
def nandTable (Y : Bool → Bool) : K := 1 - ∏ b : Bool, bit (Y b)

theorem nandTable_bit (Y : Bool → Bool) : nandTable (K := K) Y = 0 ∨ nandTable (K := K) Y = 1 := by
  cases ha : Y false <;> cases hb : Y true <;>
    simp [nandTable, bit, ha, hb]

theorem nandTable_extension (X : Bool → Bool) :
    extension (nandTable (K := K)) (fun b => -bit (X b)) = nandTable X := by
  change extension (fun y => 1 - ∏ i : Bool, bit (y i)) (fun b => -bit (X b)) = _
  rw [extension_negative_clause]
  simp [nandTable]

end Rows

section Graph

variable {V E : Type*}
variable [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Incidences of a graph with two indexed endpoints per edge. A simple
cubic graph is a special case; no regularity is needed for the algebra. -/
def independent (endpoint : E → Bool → V) (x : V → Bool) : Prop :=
  ∀ e : E, ¬ (x (endpoint e false) = true ∧ x (endpoint e true) = true)

noncomputable def independentCount (endpoint : E → Bool → V) : ℕ := by
  classical
  exact ((Finset.univ : Finset (V → Bool)).filter (independent endpoint)).card

omit [Fintype E] [DecidableEq E] in
theorem independentCount_le (endpoint : E → Bool → V) :
    independentCount endpoint ≤ 2 ^ Fintype.card V := by
  classical
  unfold independentCount
  simpa using
    (Finset.card_filter_le (s := (Finset.univ : Finset (V → Bool))) (p := independent endpoint))

omit [DecidableEq E] in
theorem independentCount_formula {K : Type*} [CommRing K] (endpoint : E → Bool → V) :
    (∑ x : V → Bool, ∏ e : E, nandTable (K := K) (x ∘ endpoint e)) =
      (independentCount endpoint : K) := by
  classical
  have term (x : V → Bool) (e : E) :
      nandTable (K := K) (x ∘ endpoint e) =
        if ¬ (x (endpoint e false) = true ∧ x (endpoint e true) = true) then 1 else 0 := by
    cases h0 : x (endpoint e false) <;> cases h1 : x (endpoint e true) <;>
      simp [nandTable, bit, h0, h1]
  simp only [term, Finset.prod_boole, Finset.mem_univ, true_implies, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    independentCount]
  apply congrArg (fun S : Finset (V → Bool) => (S.card : K))
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rfl

/-- Two physical wires for each original edge incidence, with the original
NAND rows and original equality columns on disjoint physical stars. -/
noncomputable def graphRegister {K : Type*} [CommRing K] (endpoint : E → Bool → V)
    (earlier : (Σ _ : E, Bool) → Option (Σ _ : E, Bool)) : K :=
  pairedRegister (rowProduct fun _ => nandTable)
    (equalityTensor fun i : Σ _ : E, Bool => endpoint i.1 i.2) earlier

/-- A1, exact single-register reduction at the predecessor kernel, valid even
in a finite precision ring, including coefficient signs. -/
theorem graphRegister_eq {K : Type*} [CommRing K] (endpoint : E → Bool → V)
    (earlier : (Σ _ : E, Bool) → Option (Σ _ : E, Bool))
    (onto : Function.Surjective fun i : Σ _ : E, Bool => endpoint i.1 i.2) :
    graphRegister (K := K) endpoint earlier = (independentCount endpoint : K) := by
  classical
  rw [graphRegister, pairedRegister_collapse, equalityTensor_sum _ onto, ← independentCount_formula]
  apply Finset.sum_congr rfl
  intro x hx
  rw [extension_rowProduct]
  apply Finset.prod_congr rfl
  intro e he
  exact nandTable_extension (x ∘ endpoint e)

/-- Taking `p = |V|+1` is sufficient; no losses from representatives. -/
theorem graphRegister_value (endpoint : E → Bool → V)
    (earlier : (Σ _ : E, Bool) → Option (Σ _ : E, Bool))
    (onto : Function.Surjective fun i : Σ _ : E, Bool => endpoint i.1 i.2)
    {p : ℕ} (hp : Fintype.card V < p) :
    (graphRegister (K := ZMod (2 ^ p)) endpoint earlier).val = independentCount endpoint := by
  rw [graphRegister_eq endpoint earlier onto, ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  exact (independentCount_le endpoint).trans_lt (Nat.pow_lt_pow_right (by decide) hp)

/-- Contraction on the physical wires themselves, before taking the shift:
each odd source is pinned to zero and no simulated edge couples vertices. -/
noncomputable def graphOrigin {K : Type*} [CommRing K] (endpoint : E → Bool → V) : K :=
  ∑ X : ((Σ _ : E, Bool) → Bool) × ((Σ _ : E, Bool) → Bool),
    equalityTensor (fun i : Σ _ : E, Bool => endpoint i.1 i.2) X.1 *
      (pinsZero X.2 * rowProduct (fun _ => nandTable) X.2)

theorem graphOrigin_eq {K : Type*} [CommRing K] (endpoint : E → Bool → V)
    (onto : Function.Surjective fun i : Σ _ : E, Bool => endpoint i.1 i.2) :
    graphOrigin (K := K) endpoint = (2 : K)^Fintype.card V := by
  classical
  rw [graphOrigin, Fintype.sum_prod_type]
  have hrow : (rowProduct (fun _ : E => nandTable) (fun _ => false) : K) = 1 := by
    simp [rowProduct, nandTable, bit]
  have hpin (x t : (Σ _ : E, Bool) → Bool) :
      (equalityTensor (K := K) (fun i : Σ _ : E, Bool => endpoint i.1 i.2) x *
        (pinsZero t * rowProduct (fun _ => nandTable) t)) =
      if t = (fun _ => false) then
        equalityTensor (fun i : Σ _ : E, Bool => endpoint i.1 i.2) x
      else 0 := by
    by_cases ht : t = (fun _ => false)
    · simp [ht, pinsZero_eq, hrow]
    · simp [ht, pinsZero_eq]
  simp_rw [hpin, Fintype.sum_ite_eq']
  have hsum := equalityTensor_sum (K := K)
    (fun i : Σ _ : E, Bool => endpoint i.1 i.2) onto (fun _ => 1)
  simp only [mul_one] at hsum
  rw [hsum]
  simp


end Graph

/-- The local two-port copying identity used to compile arbitrary
Boolean row tables at the shifted point in A2. -/
theorem shifted_copy_identity {K : Type*} [CommRing K] (f : Bool → K) (x : Bool) :
    (∑ y : Bool, ∑ z : Bool, f (y && z) * lag y (-bit x) * lag z (-1)) = f x := by
  cases x <;> simp [lag, bit] <;> ring


section LiteralPhysical

variable {K : Type*} [CommRing K]

def readPredecessor {I : Type*} (q : Option I) (X : I → Bool) : Bool :=
  (q.map X).getD false

/-- The normalization at this mesh point is integer exact; it is performed
before reduction rather than inverting a possibly even denominator. -/
def packetMeshKernel {I P : Type*} [DecidableEq P] (L : ℕ)
    (packet : I → P) (pos : I → ℤ) (x y : I) : ℤ :=
  if packet x = packet y then meshDeleted L (pos y - pos x) (-1) / meshDeleted L 0 0 else 0

theorem packetMeshKernel_eq {I P : Type*} [DecidableEq P] (L : ℕ) (hL : 0 < L)
    (packet : I → P) (pos : I → ℤ) (x y : I) :
    packetMeshKernel L packet pos x y =
      if packet x = packet y ∧ pos y + 1 = pos x then -1 else 0 := by
  unfold packetMeshKernel
  by_cases h : packet x = packet y
  · simp only [h, if_true, true_and]
    rw [meshDeleted_minus_one L hL, Int.mul_ediv_cancel _ (meshDeleted_den_nonzero L)]
    have offset : pos y - pos x = -1 ↔ pos y + 1 = pos x := by omega
    simp only [offset]
  · simp [h]

/-- Passing from the actual local signed Cauchy coefficients in a supplied
packing to one predecessor read, after any ring reduction. -/
theorem packetMesh_argument {I P : Type*} [Fintype I] [DecidableEq I] [DecidableEq P]
    (L : ℕ) (hL : 0 < L) (packet : I → P) (pos : I → ℤ) (pred : I → Option I)
    (correct : ∀ x y, pred x = some y ↔ packet x = packet y ∧ pos y + 1 = pos x)
    (X : I → Bool) (x : I) :
    (∑ y : I, (packetMeshKernel L packet pos x y : K) * bit (X y)) =
      -bit (readPredecessor (pred x) X) := by
  have coefficient (y : I) :
      (packetMeshKernel L packet pos x y : K) * bit (X y) =
        if pred x = some y then -bit (X y) else 0 := by
    rw [packetMeshKernel_eq L hL]
    by_cases h : pred x = some y
    · simp [h, (correct x y).mp h]
    · have hn : ¬ (packet x = packet y ∧ pos y + 1 = pos x) := fun hp => h ((correct x y).mpr hp)
      simp only [if_neg hn, if_neg h, Int.cast_zero, zero_mul]
  simp_rw [coefficient]
  cases pred x with
  | none => simp [readPredecessor, bit]
  | some i =>
    simp only [Option.some.injEq, readPredecessor, Option.map_some, Option.getD_some]
    simpa only [eq_comm] using (Fintype.sum_ite_eq' i (fun y : I => -bit (X y) : I → K))


section PairedMesh

variable {I P : Type*} [Fintype I] [DecidableEq I] [DecidableEq P]

/-- The two wires born from an incidence are named by false/even and
true/odd, respectively. -/
def pairedBits (X : (I → Bool) × (I → Bool)) (i : I × Bool) : Bool :=
  if i.2 then X.2 i.1 else X.1 i.1

/-- A1's original doubled-star sum with the local polynomial kernel exposed. -/
def pairedMeshRegister (row col : (I → Bool) → K)
    (L : ℕ) (packet : I × Bool → P) (position : I × Bool → ℤ) : K :=
  ∑ X : (I → Bool) × (I → Bool), ∑ Y : (I → Bool) × (I → Bool),
    (col X.1 * pinsZero X.2) *
      ((row Y.2 * (∏ i : I, lag (Y.2 i) (∑ j : I × Bool,
          (packetMeshKernel L packet position (i,true) j : K) * bit (pairedBits X j)))) *
        (∏ i : I, lag (Y.1 i) (∑ j : I × Bool,
          (packetMeshKernel L packet position (i,false) j : K) * bit (pairedBits X j))))

theorem pairedMeshRegister_eq (row col : (I → Bool) → K)
    (L : ℕ) (hL : 0 < L) (packet : I × Bool → P) (position : I × Bool → ℤ)
    (earlier : I → Option I) (pred : I × Bool → Option (I × Bool))
    (placement : ∀ x y, pred x = some y ↔ packet x = packet y ∧ position y + 1 = position x)
    (odd : ∀ i, pred (i,true) = some (i,false))
    (even : ∀ i, pred (i,false) = (earlier i).map (fun j => (j,true))) :
    pairedMeshRegister row col L packet position = pairedRegister row col earlier := by
  have leftSource (X : (I → Bool) × (I → Bool)) (i : I) :
      readPredecessor (pred (i,false)) (pairedBits X) = ((earlier i).map X.2).getD false := by
    rw [even]
    cases earlier i <;> rfl
  have rightSource (X : (I → Bool) × (I → Bool)) (i : I) :
      readPredecessor (pred (i,true)) (pairedBits X) = X.1 i := by
    rw [odd]
    rfl
  simp only [pairedMeshRegister, pairedRegister]
  simp_rw [packetMesh_argument L hL packet position pred placement, leftSource, rightSource]

end PairedMesh

/-- A1 exact recovery from the normalized Cauchy sum itself. The finite
placement predicates encode the supplied packet layout, not a rank or
value premise about the answer. -/
theorem graphMeshRegister_value {V E P : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [DecidableEq P]
    (endpoint : E → Bool → V)
    (onto : Function.Surjective fun i : Σ _ : E, Bool => endpoint i.1 i.2)
    (L : ℕ) (hL : 0 < L)
    (packet : (Σ _ : E, Bool) × Bool → P) (position : (Σ _ : E, Bool) × Bool → ℤ)
    (earlier : (Σ _ : E, Bool) → Option (Σ _ : E, Bool))
    (pred : (Σ _ : E, Bool) × Bool → Option ((Σ _ : E, Bool) × Bool))
    (placement : ∀ x y, pred x = some y ↔ packet x = packet y ∧ position y + 1 = position x)
    (odd : ∀ i, pred (i,true) = some (i,false))
    (even : ∀ i, pred (i,false) = (earlier i).map (fun j => (j,true)))
    {p : ℕ} (hp : Fintype.card V < p) :
    (pairedMeshRegister (K := ZMod (2^p)) (rowProduct fun _ => nandTable)
      (equalityTensor fun i : Σ _ : E, Bool => endpoint i.1 i.2) L packet position).val =
      independentCount endpoint := by
  rw [pairedMeshRegister_eq _ _ L hL packet position earlier pred placement odd even]
  exact graphRegister_value endpoint earlier onto hp


/-- One bit vector each for the clause row ports and the unary variable row
ports, in the CNF with a distinct variable per literal occurrence. -/
def splitLiteralAssignments (I : Type*) :
    ((I × Bool) → Bool) ≃ ((I → Bool) × (I → Bool)) where
  toFun b := (fun i => b (i,true), fun i => b (i,false))
  invFun b i := if i.2 then b.1 i.1 else b.2 i.1
  left_inv b := by
    funext p
    rcases p with ⟨i,q⟩
    cases q <;> rfl
  right_inv b := by
    cases b
    rfl

/-- Literal sparse conversion with two distinct physical wires and one
two-port equality column per occurrence, and an all-ones unary variable row.
The supplied tap is the predecessor address in the physical packing. -/
noncomputable def literalShiftedRegister {R W : Type*}
    [Fintype R] [DecidableEq R] [Fintype W] {J : R → Type*}
    [(r : R) → Fintype (J r)] [(r : R) → DecidableEq (J r)]
    (table : (r : R) → (J r → Bool) → K) (cols : (Σ r, J r) ≃ W)
    (tap : ((Σ r, J r) × Bool) → Option ((Σ r, J r) × Bool)) : K :=
  ∑ X : ((Σ r, J r) × Bool) → Bool,
    equalityTensor (cols ∘ Prod.fst) X *
      ∑ Y : ((Σ r, J r) × Bool) → Bool,
        rowProduct table (fun i => Y (i,true)) *
          ∏ i : (Σ r, J r) × Bool, lag (Y i) (-bit (readPredecessor (tap i) X))

/-- The literal physical sum with the actual normalized mesh coefficients.
Passing to the finite residue ring is performed on the integer coefficients. -/
noncomputable def literalMeshRegister {R W P : Type*}
    [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq P] {J : R → Type*}
    [(r : R) → Fintype (J r)] [(r : R) → DecidableEq (J r)]
    (table : (r : R) → (J r → Bool) → K) (cols : (Σ r, J r) ≃ W)
    (L : ℕ) (packet : ((Σ r, J r) × Bool) → P) (pos : ((Σ r, J r) × Bool) → ℤ) : K :=
  ∑ X : ((Σ r, J r) × Bool) → Bool,
    equalityTensor (cols ∘ Prod.fst) X *
      ∑ Y : ((Σ r, J r) × Bool) → Bool,
        rowProduct table (fun i => Y (i,true)) *
          ∏ i : (Σ r, J r) × Bool, lag (Y i) (∑ j : (Σ r, J r) × Bool,
            (packetMeshKernel L packet pos i j : K) * bit (X j))

theorem literalMeshRegister_eq {R W P : Type*}
    [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq P] {J : R → Type*}
    [(r : R) → Fintype (J r)] [(r : R) → DecidableEq (J r)]
    (table : (r : R) → (J r → Bool) → K) (cols : (Σ r, J r) ≃ W)
    (L : ℕ) (hL : 0 < L) (packet : ((Σ r, J r) × Bool) → P) (pos : ((Σ r, J r) × Bool) → ℤ)
    (pred : ((Σ r, J r) × Bool) → Option ((Σ r, J r) × Bool))
    (placement : ∀ x y, pred x = some y ↔ packet x = packet y ∧ pos y + 1 = pos x) :
    literalMeshRegister table cols L packet pos = literalShiftedRegister table cols pred := by
  simp only [literalMeshRegister, literalShiftedRegister]
  simp_rw [packetMesh_argument L hL packet pos pred placement]


theorem literalShiftedRegister_eq {R W : Type*}
    [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W] {J : R → Type*}
    [(r : R) → Fintype (J r)] [(r : R) → DecidableEq (J r)]
    (table : (r : R) → (J r → Bool) → K) (cols : (Σ r, J r) ≃ W)
    (tap : ((Σ r, J r) × Bool) → Option ((Σ r, J r) × Bool)) :
    literalShiftedRegister table cols tap =
      ∑ X : W → Bool, ∏ r : R,
        extension (table r) (fun j =>
          -bit (readPredecessor ((tap (⟨r,j⟩,true)).map (cols ∘ Prod.fst)) X)) := by
  classical
  let I := Σ r, J r
  have onto : Function.Surjective (cols ∘ (Prod.fst : I × Bool → I)) := by
    intro w
    exact ⟨(cols.symm w, false), cols.apply_symm_apply w⟩
  rw [literalShiftedRegister, equalityTensor_sum _ onto]
  apply Finset.sum_congr rfl
  intro X hX
  let a : I × Bool → K := fun i => -bit (readPredecessor (tap i) (X ∘ cols ∘ Prod.fst))
  let aa : I → K := fun i => a (i,true)
  let ab : I → K := fun i => a (i,false)
  have prod_split (Y : I × Bool → Bool) :
      (∏ i : I × Bool, lag (Y i) (a i)) =
        (∏ i : I, lag (Y (i,true)) (aa i)) * ∏ i : I, lag (Y (i,false)) (ab i) := by
    rw [Fintype.prod_prod_type]
    simpa only [Fintype.prod_bool, aa, ab] using
      (Finset.prod_mul_distrib (s := (Finset.univ : Finset I))
        (f := fun i => lag (Y (i,true)) (a (i,true)))
        (g := fun i => lag (Y (i,false)) (a (i,false))))
  let f : (I → Bool) → K := fun v => rowProduct table v * ∏ i : I, lag (v i) (aa i)
  let g : (I → Bool) → K := fun u => ∏ i : I, lag (u i) (ab i)
  have hs :
      (∑ Y : (I × Bool) → Bool, rowProduct table (fun i => Y (i,true)) *
        ∏ i : I × Bool, lag (Y i) (a i)) =
          ∑ Z : (I → Bool) × (I → Bool), f Z.1 * g Z.2 := by
    apply Fintype.sum_equiv (splitLiteralAssignments I)
    intro Y
    rw [prod_split]
    exact (mul_assoc _ _ _).symm
  change (∑ Y : I × Bool → Bool, rowProduct table (fun i => Y (i,true)) *
    ∏ i : I × Bool, lag (Y i) (a i)) = _
  rw [hs, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  have hg : (∑ u : I → Bool, g u) = 1 := by
    simpa only [extension, one_mul] using
      (extension_one ab : extension (fun _ => (1 : K)) ab = 1)
  rw [hg, mul_one]
  change extension (rowProduct table) aa = _
  rw [extension_rowProduct]
  apply Finset.prod_congr rfl
  intro r hr
  congr 1
  funext j
  simp only [aa, a, readPredecessor, Option.map_map]

end LiteralPhysical


section EdgeCover

variable {E V₂ V₃ U C : Type*}
variable [Fintype E] [DecidableEq E] [Fintype V₂] [DecidableEq V₂]
variable [Fintype V₃] [DecidableEq V₃] [Fintype U] [DecidableEq U]
variable [Fintype C] [DecidableEq C]

/-- A zero bit means the edge is selected, as in the literal reduction. -/
def isCover (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E) (x : E → Bool) : Prop :=
  (∀ v : V₂, ∃ i : Fin 2, x (at₂ v i) = false) ∧
  (∀ v : V₃, ∃ i : Fin 3, x (at₃ v i) = false)

noncomputable def coverCount (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E) : ℕ := by
  classical
  exact ((Finset.univ : Finset (E → Bool)).filter (isCover at₂ at₃)).card

omit [Fintype V₂] [DecidableEq V₂] [Fintype V₃] [DecidableEq V₃] in
theorem coverCount_le (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E) :
    coverCount at₂ at₃ ≤ 2 ^ Fintype.card E := by
  classical
  unfold coverCount
  simpa using (Finset.card_filter_le (s := (Finset.univ : Finset (E → Bool)))
    (p := isCover at₂ at₃))

variable {K : Type*} [CommRing K]

/-- Sign of a product with one negative factor for each index. -/
theorem prod_neg_sign {I : Type*} [Fintype I] (f : I → K) :
    (∏ i : I, - f i) = (-1 : K) ^ Fintype.card I * ∏ i : I, f i := by
  have fun_eq : (fun i => - f i) = fun i => (-1 : K) * f i := by
    funext i
    exact (neg_one_mul (f i)).symm
  rw [fun_eq, Finset.prod_mul_distrib]
  simp

theorem neg_one_pow_of_even {n : ℕ} (h : Even n) : (-1 : K) ^ n = 1 := by
  obtain ⟨m, hm⟩ := h
  rw [hm, ← two_mul, pow_mul]
  simp

theorem extension_even_negative_clause {I : Type*} [Fintype I] [DecidableEq I]
    (even : Even (Fintype.card I)) (X : I → Bool) :
    extension (fun y => 1 - ∏ i : I, bit (y i)) (fun i => -bit (X i) : I → K) =
      1 - ∏ i : I, bit (X i) := by
  rw [extension_negative_clause, prod_neg_sign, neg_one_pow_of_even even, one_mul]

/-- A planted width-four negative row and a positive unary use the same
auxiliary bit. Their actual signed product is used before summing that bit. -/
def hardenedCoverWeight (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E)
    (x : E → Bool) (b : V₃ → Bool) : K :=
  (∏ v : V₂, (1 - ∏ i : Fin 2, bit (x (at₂ v i)))) *
  (∏ v : V₃, ((1 - (∏ i : Fin 3, bit (x (at₃ v i))) * bit (b v)) * (-bit (b v))))

theorem signed_aux_sum (q : K) :
    (∑ b : Bool, (1 - q * bit b) * (-bit b)) = -(1-q) := by
  simp [bit]

theorem negativeClause_indicator {J : Type*} [Fintype J] (x : J → Bool) :
    (1 - ∏ i : J, bit (x i) : K) = if ∃ i, x i = false then 1 else 0 := by
  classical
  by_cases h : ∃ i, x i = false
  · obtain ⟨i, hi⟩ := h
    have z : (∏ j : J, bit (x j) : K) = 0 := by
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [bit, hi])
    rw [if_pos ⟨i, hi⟩, z, sub_zero]
  · rw [if_neg h]
    have o : (∏ j : J, bit (x j) : K) = 1 := by
      apply Finset.prod_eq_one
      intro j _
      cases hj : x j
      · exact (h ⟨j,hj⟩).elim
      · simp [bit]
    rw [o, sub_self]


omit [DecidableEq V₂] in
theorem hardenedCover_sum (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E)
    (even : Even (Fintype.card V₃)) :
    (∑ x : E → Bool, ∑ b : V₃ → Bool, hardenedCoverWeight (K := K) at₂ at₃ x b) =
      (coverCount at₂ at₃ : K) := by
  classical
  have hsum (x : E → Bool) : (∑ b : V₃ → Bool, hardenedCoverWeight (K := K) at₂ at₃ x b) =
      if isCover at₂ at₃ x then 1 else 0 := by
    simp only [hardenedCoverWeight, ← Finset.mul_sum]
    rw [← Fintype.prod_sum (fun v (b : Bool) =>
      (1 - (∏ i : Fin 3, bit (x (at₃ v i))) * bit b) * (-bit b))]
    simp only [signed_aux_sum, prod_neg_sign, neg_one_pow_of_even (K := K) even, one_mul]
    by_cases h₂ : ∀ v : V₂, ∃ i : Fin 2, x (at₂ v i) = false
    · have hleft : (∏ v : V₂, (1 - ∏ i : Fin 2, bit (x (at₂ v i))) : K) = 1 :=
        Finset.prod_eq_one (fun v _ =>
          (negativeClause_indicator (fun i : Fin 2 => x (at₂ v i))).trans (if_pos (h₂ v)))
      rw [hleft, one_mul]
      by_cases h₃ : ∀ v : V₃, ∃ i : Fin 3, x (at₃ v i) = false
      · rw [if_pos ⟨h₂,h₃⟩]
        exact Finset.prod_eq_one (fun v _ =>
          (negativeClause_indicator (fun i : Fin 3 => x (at₃ v i))).trans (if_pos (h₃ v)))
      · rw [if_neg (fun h => h₃ h.2)]
        obtain ⟨v,hv⟩ := not_forall.mp h₃
        exact Finset.prod_eq_zero (Finset.mem_univ v)
          ((negativeClause_indicator (fun i : Fin 3 => x (at₃ v i))).trans (if_neg hv))
    · rw [if_neg (fun h => h₂ h.1)]
      obtain ⟨v,hv⟩ := not_forall.mp h₂
      have hz : (∏ v : V₂, (1 - ∏ i : Fin 2, bit (x (at₂ v i))) : K) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ v)
          ((negativeClause_indicator (fun i : Fin 2 => x (at₂ v i))).trans (if_neg hv))
      rw [hz, zero_mul]
  simp_rw [hsum]
  rw [← Finset.sum_filter]
  simp [coverCount]

/-- Even number of degree-three vertices follows from the incidence count. -/
theorem odd_vertex_count_even {n₂ n₃ m : ℕ} (h : 2*n₂ + 3*n₃ = 2*m) : Even n₃ := by
  refine ⟨n₃ / 2, ?_⟩
  omega

/-- Number of matched negative unary rows fed by a given spare subdivision
column. Unmatched rows have no effect. -/
def unaryLoad (tap : U → Option C) (c : C) : ℕ := Fintype.card {u : U // tap u = some c}

def publicFactor (tap : U → Option C) : ℕ := ∏ c : C, (1 + 2 ^ unaryLoad tap c)

def fillerWeight (tap : U → Option C) (bits : C → Bool) : K :=
  ∏ u : U, (1 + bit (((tap u).map bits).getD false))

omit [DecidableEq U] in
theorem fillerWeight_fiber (tap : U → Option C) (bits : C → Bool) :
    fillerWeight (K := K) tap bits = ∏ c : C, (if bits c then 2 else 1) ^ unaryLoad tap c := by
  classical
  unfold fillerWeight
  rw [← Fintype.prod_fiberwise' tap (fun z => 1 + bit ((z.map bits).getD false)),
    Fintype.prod_option]
  simp only [Option.map_none, Option.getD_none, bit, Bool.false_eq_true, if_false, add_zero,
    Finset.prod_const_one, one_mul]
  apply Finset.prod_congr rfl
  intro c hc
  rw [Finset.prod_const]
  cases h : bits c <;> norm_num [h, unaryLoad]

omit [DecidableEq U] in
theorem fillerWeight_sum (tap : U → Option C) :
    (∑ bits : C → Bool, fillerWeight (K := K) tap bits) = (publicFactor tap : K) := by
  simp_rw [fillerWeight_fiber]
  rw [← Fintype.prod_sum (fun c (b : Bool) => (if b then (2 : K) else 1) ^ unaryLoad tap c)]
  simp only [publicFactor, Nat.cast_prod, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
  apply Finset.prod_congr rfl
  intro c hc
  simp [add_comm]

/-- The sum with independent edge bits, auxiliary pin bits and padding
column bits, after the Boolean row extensions. -/
def selectedLiteralRegister (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E)
    (tap : U → Option C) : K :=
  ∑ x : E → Bool, ∑ b : V₃ → Bool, ∑ z : C → Bool,
      hardenedCoverWeight at₂ at₃ x b * fillerWeight tap z

omit [DecidableEq V₂] [DecidableEq U] in
theorem selectedLiteralRegister_eq (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E)
    (tap : U → Option C) (even : Even (Fintype.card V₃)) :
    selectedLiteralRegister (K := K) at₂ at₃ tap =
      (coverCount at₂ at₃ * publicFactor tap : ℕ) := by
  simp only [selectedLiteralRegister, ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hardenedCover_sum at₂ at₃ even, fillerWeight_sum]
  push_cast
  rfl

omit [DecidableEq U] in
theorem publicFactor_pos (tap : U → Option C) : 0 < publicFactor tap := by
  unfold publicFactor
  exact Finset.prod_pos (fun c _ => Nat.add_pos_left Nat.one_pos _)

omit [DecidableEq U] in
theorem publicFactor_le (tap : U → Option C) (h : ∀ c, unaryLoad tap c ≤ 2) :
    publicFactor tap ≤ 5 ^ Fintype.card C := by
  unfold publicFactor
  calc
    (∏ c : C, (1 + 2 ^ unaryLoad tap c)) ≤ ∏ _c : C, (5 : ℕ) := by
      apply Finset.prod_le_prod
      · exact fun _ _ => Nat.zero_le _
      · intro c _
        have h' := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (h c)
        omega
    _ = _ := by simp

omit [DecidableEq V₂] [DecidableEq U] in
/-- Exact integer postprocessing of the one register, not division in the
residue ring. Precision bound stated in bits of the full integer product. -/
theorem selectedLiteralRegister_decode (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E)
    (tap : U → Option C) (even : Even (Fintype.card V₃)) {p : ℕ}
    (hp : coverCount at₂ at₃ * publicFactor tap < 2^p) :
    (selectedLiteralRegister (K := ZMod (2^p)) at₂ at₃ tap).val / publicFactor tap =
      coverCount at₂ at₃ := by
  rw [selectedLiteralRegister_eq at₂ at₃ tap even, ZMod.val_natCast, Nat.mod_eq_of_lt hp,
    Nat.mul_div_cancel _ (publicFactor_pos tap)]

end EdgeCover


section LiteralReduction

abbrev CoverRow (V₂ V₃ U : Type*) := V₂ ⊕ (V₃ ⊕ (V₃ ⊕ U))

abbrev CoverCol (E V₃ C : Type*) := E ⊕ (V₃ ⊕ C)

/-- Actual literal widths, with a distinct fourth port for each cubic vertex. -/
def CoverPort {V₂ V₃ U : Type*} : CoverRow V₂ V₃ U → Type
  | .inl _ => Fin 2
  | .inr (.inl _) => Fin 3 ⊕ Unit
  | .inr (.inr _) => Unit

instance {V₂ V₃ U : Type*} (r : CoverRow V₂ V₃ U) : Fintype (CoverPort r) :=
  match r with
  | .inl _ => inferInstanceAs (Fintype (Fin 2))
  | .inr (.inl _) => inferInstanceAs (Fintype (Fin 3 ⊕ Unit))
  | .inr (.inr _) => inferInstanceAs (Fintype Unit)

instance {V₂ V₃ U : Type*} (r : CoverRow V₂ V₃ U) : DecidableEq (CoverPort r) :=
  match r with
  | .inl _ => inferInstanceAs (DecidableEq (Fin 2))
  | .inr (.inl _) => inferInstanceAs (DecidableEq (Fin 3 ⊕ Unit))
  | .inr (.inr _) => inferInstanceAs (DecidableEq Unit)

abbrev CoverOccurrences (V₂ V₃ U : Type*) := Σ r : CoverRow V₂ V₃ U, CoverPort r

variable {E V₂ V₃ U C : Type*}
variable [Fintype E] [DecidableEq E] [Fintype V₂] [DecidableEq V₂]
variable [Fintype V₃] [DecidableEq V₃] [Fintype U] [DecidableEq U]
variable [Fintype C] [DecidableEq C]
variable {K : Type*} [CommRing K]

/-- Genuine old CNF tables: negative width-two and width-four clauses,
positive unary auxiliary clauses, negative unary padding. -/
def coverTables : (r : CoverRow V₂ V₃ U) → (CoverPort r → Bool) → K
  | .inl _, y => 1 - ∏ i : Fin 2, bit (y i)
  | .inr (.inl _), y => 1 - ∏ i : Fin 3 ⊕ Unit, bit (y i)
  | .inr (.inr (.inl _)), y => ∏ i : Unit, bit (y i)
  | .inr (.inr (.inr _)), y => 1 - ∏ i : Unit, bit (y i)

/-- The planted layout protocol on the column names. This states locations,
not arithmetic values. An actual source layout may be checked against it. -/
def coverSources (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E)
    (stray : U → Option C) : (r : CoverRow V₂ V₃ U) → CoverPort r → Option (CoverCol E V₃ C)
  | .inl v, p => some (.inl (at₂ v p))
  | .inr (.inl v), .inl p => some (.inl (at₃ v p))
  | .inr (.inl v), .inr _ => some (.inr (.inl v))
  | .inr (.inr (.inl v)), _ => some (.inr (.inl v))
  | .inr (.inr (.inr u)), _ => (stray u).map (fun c => .inr (.inr c))

def splitCoverColumns :
    (CoverCol E V₃ C → Bool) ≃ ((E → Bool) × ((V₃ → Bool) × (C → Bool))) :=
  (Equiv.sumArrowEquivProdArrow E (V₃ ⊕ C) Bool).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.sumArrowEquivProdArrow V₃ C Bool))

omit [Fintype E] [DecidableEq E] [DecidableEq V₂] [DecidableEq V₃]
    [DecidableEq U] [Fintype C] [DecidableEq C] in
theorem coverTables_product (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E)
    (stray : U → Option C) (X : CoverCol E V₃ C → Bool) :
    (∏ r : CoverRow V₂ V₃ U, extension (coverTables (K := K) r) (fun j =>
      -bit (readPredecessor (coverSources at₂ at₃ stray r j) X))) =
    hardenedCoverWeight at₂ at₃ (fun e => X (.inl e)) (fun v => X (.inr (.inl v))) *
      fillerWeight stray (fun c => X (.inr (.inr c))) := by
  let f : CoverRow V₂ V₃ U → K := fun r =>
    extension (coverTables r) (fun j => -bit (readPredecessor (coverSources at₂ at₃ stray r j) X))
  have two (v : V₂) : f (.inl v) = 1 - ∏ j : Fin 2, bit (X (.inl (at₂ v j))) := by
    change extension (fun y => 1 - ∏ i : Fin 2, bit (y i))
      (fun j => -bit (X (.inl (at₂ v j)))) = _
    exact extension_even_negative_clause (by exact ⟨1, by decide⟩) _
  have four (v : V₃) : f (.inr (.inl v)) =
      1 - (∏ j : Fin 3, bit (X (.inl (at₃ v j)))) * bit (X (.inr (.inl v))) := by
    let y : Fin 3 ⊕ Unit → Bool := Sum.elim (fun j => X (.inl (at₃ v j))) (fun _ => X (.inr (.inl v)))
    change extension (fun j => 1 - ∏ i : Fin 3 ⊕ Unit, bit (j i)) (fun j => -bit (y j)) = _
    rw [extension_even_negative_clause (by exact ⟨2, by decide⟩), Fintype.prod_sum_type]
    simp [y]
  have pin (v : V₃) : f (.inr (.inr (.inl v))) = -bit (X (.inr (.inl v))) := by
    change extension (fun y => ∏ i : Unit, bit (y i)) (fun _ => -bit (X (.inr (.inl v)))) = _
    rw [extension_full_monomial]
    simp
  have pad (u : U) : f (.inr (.inr (.inr u))) = 1 + bit (((stray u).map
      (fun c => X (.inr (.inr c)))).getD false) := by
    change extension (fun y => 1 - ∏ i : Unit, bit (y i))
        (fun _ => -bit (readPredecessor ((stray u).map (fun c => .inr (.inr c))) X)) = _
    rw [extension_negative_clause]
    simp [readPredecessor, Option.map_map, Function.comp_def]
  change (∏ r, f r) = _
  rw [Fintype.prod_sum_type f, Fintype.prod_sum_type (fun r => f (.inr r)),
    Fintype.prod_sum_type (fun r => f (.inr (.inr r)))]
  simp only [two, four, pin, pad, hardenedCoverWeight, fillerWeight, Finset.prod_mul_distrib]
  ring

/-- A4 equation (A6) on the physical literal input. The only layout premise
is that the actual predecessor ports have the specified column addresses. -/
theorem literalCoverRegister_eq
    (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E) (stray : U → Option C)
    (cols : CoverOccurrences V₂ V₃ U ≃ CoverCol E V₃ C)
    (tap : (CoverOccurrences V₂ V₃ U × Bool) → Option (CoverOccurrences V₂ V₃ U × Bool))
    (planted : ∀ (r : CoverRow V₂ V₃ U) (j : CoverPort r),
      (tap (⟨r,j⟩,true)).map (cols ∘ Prod.fst) = coverSources at₂ at₃ stray r j)
    (even : Even (Fintype.card V₃)) :
    literalShiftedRegister (coverTables (K := K)) cols tap =
      (coverCount at₂ at₃ * publicFactor stray : ℕ) := by
  rw [literalShiftedRegister_eq]
  simp_rw [planted, coverTables_product]
  rw [← selectedLiteralRegister_eq at₂ at₃ stray even]
  let h : (E → Bool) × ((V₃ → Bool) × (C → Bool)) → K := fun x =>
    hardenedCoverWeight at₂ at₃ x.1 x.2.1 * fillerWeight stray x.2.2
  have joined : (selectedLiteralRegister (K := K) at₂ at₃ stray) = ∑ x, h x := by
    simp only [selectedLiteralRegister, Fintype.sum_prod_type, h]
  rw [joined]
  apply Fintype.sum_equiv (splitCoverColumns (E := E) (V₃ := V₃) (C := C))
  intro X
  rfl

omit [Fintype V₂] [DecidableEq V₂] [Fintype V₃] [DecidableEq V₃] [DecidableEq U] in
/-- With at most two incoming taps per spare equality column, any root
precision above 2M suffices when each listed column has two physical wires
and the number of input edges is at most M/2. -/
theorem literalCover_precision
    (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E) (stray : U → Option C)
    (load : ∀ c, unaryLoad stray c ≤ 2) {M p : ℕ}
    (hE : 2 * Fintype.card E ≤ M) (hC : 2 * Fintype.card C ≤ M) (hp : 2*M < p) :
    coverCount at₂ at₃ * publicFactor stray < 2^p := by
  calc
    coverCount at₂ at₃ * publicFactor stray ≤ 2 ^ Fintype.card E * 5 ^ Fintype.card C :=
      Nat.mul_le_mul (coverCount_le at₂ at₃) (publicFactor_le stray load)
    _ ≤ 2 ^ Fintype.card E * (2^3) ^ Fintype.card C := by
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)
    _ = 2 ^ (Fintype.card E + 3 * Fintype.card C) := by rw [← pow_mul, ← pow_add]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

/-- A4 postprocessing, from the physical register at its finite precision
to the true edge-cover count. The divisor is public and is used *after*
taking the exact nonnegative representative. -/
theorem literalCoverRegister_decode
    (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E) (stray : U → Option C)
    (cols : CoverOccurrences V₂ V₃ U ≃ CoverCol E V₃ C)
    (tap : (CoverOccurrences V₂ V₃ U × Bool) → Option (CoverOccurrences V₂ V₃ U × Bool))
    (planted : ∀ (r : CoverRow V₂ V₃ U) (j : CoverPort r),
      (tap (⟨r,j⟩,true)).map (cols ∘ Prod.fst) = coverSources at₂ at₃ stray r j)
    (even : Even (Fintype.card V₃)) (load : ∀ c, unaryLoad stray c ≤ 2)
    {M p : ℕ} (hE : 2*Fintype.card E ≤ M) (hC : 2*Fintype.card C ≤ M) (hp : 2*M < p) :
    (literalShiftedRegister (coverTables (K := ZMod (2^p))) cols tap).val / publicFactor stray =
      coverCount at₂ at₃ := by
  rw [literalCoverRegister_eq at₂ at₃ stray cols tap planted even,
    ZMod.val_natCast, Nat.mod_eq_of_lt (literalCover_precision at₂ at₃ stray load hE hC hp),
    Nat.mul_div_cancel _ (publicFactor_pos stray)]

omit [DecidableEq U] [Fintype C] in
/-- Injective use of actual predecessor wires implies the bound of two per
spare subdivision column with exactly two ports. -/
theorem unaryLoad_le_two_of_ports (stray : U → Option C) (phys : U → Option (C × Bool))
    (projects : ∀ u, (phys u).map Prod.fst = stray u)
    (nonreuse : ∀ u v c b, phys u = some (c,b) → phys v = some (c,b) → u = v)
    (c : C) : unaryLoad stray c ≤ 2 := by
  let chosen (u : {u : U // stray u = some c}) : Bool :=
    ((phys u.1).getD (c,false)).2
  have spec (u : {u : U // stray u = some c}) : phys u.1 = some (c,chosen u) := by
    have eq := (projects u.1).trans u.2
    cases hx : phys u.1 with
    | none => simp [hx] at eq
    | some pair =>
      rcases pair with ⟨z,b⟩
      have hc : z = c := by simpa [hx] using eq
      subst z
      simp [chosen, hx]
  have inj : Function.Injective chosen := by
    intro u v h
    apply Subtype.ext
    exact nonreuse u.1 v.1 c (chosen u) (spec u) (by rw [h]; exact spec v)
  unfold unaryLoad
  simpa only [Fintype.card_bool] using Fintype.card_le_of_injective chosen inj


/-- A4 exact recovery directly from the normalized Cauchy register,
given its certified physical predecessor placement. -/
theorem literalMeshCoverRegister_decode {P : Type*} [DecidableEq P]
    (at₂ : V₂ → Fin 2 → E) (at₃ : V₃ → Fin 3 → E) (stray : U → Option C)
    (cols : CoverOccurrences V₂ V₃ U ≃ CoverCol E V₃ C)
    (L : ℕ) (hL : 0 < L)
    (packet : (CoverOccurrences V₂ V₃ U × Bool) → P) (pos : (CoverOccurrences V₂ V₃ U × Bool) → ℤ)
    (tap : (CoverOccurrences V₂ V₃ U × Bool) → Option (CoverOccurrences V₂ V₃ U × Bool))
    (placement : ∀ x y, tap x = some y ↔ packet x = packet y ∧ pos y + 1 = pos x)
    (planted : ∀ (r : CoverRow V₂ V₃ U) (j : CoverPort r),
      (tap (⟨r,j⟩,true)).map (cols ∘ Prod.fst) = coverSources at₂ at₃ stray r j)
    (even : Even (Fintype.card V₃)) (load : ∀ c, unaryLoad stray c ≤ 2)
    {M p : ℕ} (hE : 2*Fintype.card E ≤ M) (hC : 2*Fintype.card C ≤ M) (hp : 2*M < p) :
    (literalMeshRegister (coverTables (K := ZMod (2^p))) cols L packet pos).val /
        publicFactor stray = coverCount at₂ at₃ := by
  rw [literalMeshRegister_eq _ _ L hL packet pos tap placement]
  exact literalCoverRegister_decode at₂ at₃ stray cols tap planted even load hE hC hp


end LiteralReduction


section AcceptingPaths

/-- The additional bounded guessed number below a nonnegative witness weight.
The encoding has exactly one accepting guess for each integer below the weight. -/
def boundedGuessEquiv {q w : ℕ} (h : w ≤ q) :
    {d : Fin q // (d : ℕ) < w} ≃ Fin w where
  toFun d := ⟨d.1.1, d.2⟩
  invFun d := ⟨⟨d.1, d.2.trans_le h⟩, d.2⟩
  left_inv d := by
    apply Subtype.ext
    exact Fin.ext rfl
  right_inv d := Fin.ext rfl

/-- Reduction of a coordinate's signed residue-weighted sum to an ordinary
count of accepting pairs, including carry propagation on reduction. The
mode expansion supplying the finite witness set is separate. -/
theorem residueWeight_sum_as_count {A : Type*} [Fintype A] {q : ℕ} [NeZero q]
    (weight : A → ZMod q) :
    (Fintype.card (Σ a : A, {d : Fin q // (d : ℕ) < (weight a).val}) : ZMod q) =
      ∑ a : A, weight a := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Fintype.card_congr (boundedGuessEquiv (ZMod.val_lt (weight a)).le),
    Fintype.card_fin, ZMod.natCast_zmod_val]

end AcceptingPaths


#print axioms meshDeleted_minus_one
#print axioms cauchy_minus_one
#print axioms packetMesh_argument
#print axioms pairedRegister_collapse
#print axioms graphRegister_eq
#print axioms graphRegister_value
#print axioms graphMeshRegister_value
#print axioms graphOrigin_eq
#print axioms shifted_copy_identity
#print axioms literalCoverRegister_eq
#print axioms literalCoverRegister_decode
#print axioms literalMeshCoverRegister_decode
#print axioms unaryLoad_le_two_of_ports
#print axioms residueWeight_sum_as_count

end Acquisition
