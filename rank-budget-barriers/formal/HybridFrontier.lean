import GuardedBarrier

/-! Shared affine registers, a matrix frontier on one flattening, and
same-leaf cost accounting. The geometry producing a common flattening is
separate from the matrix and execution arguments in this file. -/

namespace HybridFrontier

open scoped BigOperators

section Rank

variable {R C K : Type*} [Fintype C] [Field K]

/-- A factorization through exactly the dimension of the matrix image. -/
theorem exact_factorization (A : Matrix R C K) :
    ∃ (L : Matrix R (Fin A.rank) K) (H : Matrix (Fin A.rank) C K), A = L * H := by
  classical
  let U := LinearMap.range A.mulVecLin
  let b : Module.Basis (Fin A.rank) K U := Module.finBasis K U
  let col (j : C) : U := A.mulVecLin.rangeRestrict (Pi.single j 1)
  refine ⟨fun r i => (b i : R → K) r, fun i c => b.repr (col c) i, ?_⟩
  ext r c
  have h := congrArg (fun v : U => (v : R → K) r) (b.sum_repr (col c))
  calc
    A r c = (col c : R → K) r := by
      change A r c = A.mulVec (Pi.single c 1) r
      rw [Matrix.mulVec_single_one]
      rfl
    _ = _ := by
      simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
        Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, mul_comm] using h.symm

/-- On a fixed evaluation flattening, scalar pointwise multiplication is
the entrywise matrix product. -/
def entryProd (A B : Matrix R C K) : Matrix R C K :=
  Matrix.of fun r c => A r c * B r c

/-- The ordinary rank bound holds for genuine matrix rank, with no given
decomposition or bound on either factor. -/
theorem rank_entryProd (A B : Matrix R C K) : (entryProd A B).rank ≤ A.rank * B.rank := by
  classical
  obtain ⟨U, V, hA⟩ := exact_factorization A
  obtain ⟨W, Z, hB⟩ := exact_factorization B
  let L : Matrix R (Fin A.rank × Fin B.rank) K := fun r p => U r p.1 * W r p.2
  let H : Matrix (Fin A.rank × Fin B.rank) C K := fun p c => V p.1 c * Z p.2 c
  have hentry (r : R) (c : C) : A r c = ∑ i, U r i * V i c := by
    exact congrFun (congrFun hA r) c
  have hentry' (r : R) (c : C) : B r c = ∑ j, W r j * Z j c := by
    exact congrFun (congrFun hB r) c
  have hfac : entryProd A B = L * H := by
    ext r c
    simp only [entryProd, Matrix.of_apply, hentry r c, hentry' r c,
      Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul, Finset.mul_sum, L, H]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ac_rfl
  rw [hfac]
  simpa using (Matrix.rank_mul_le_left L H).trans L.rank_le_card_width

variable {J : Type*} [Fintype J] [Fintype R]

/-- One charge per distinct entrance, with the accumulated transfer and
the raw-input bypass both present. -/
theorem affine_rank_budget (bypass : Matrix R C K) (weights atoms : J → Matrix R C K) :
    (bypass + ∑ j, entryProd (weights j) (atoms j)).rank ≤
      bypass.rank + ∑ j, (weights j).rank * (atoms j).rank := by
  refine (SeparatedRank.rank_add_le _ _).trans (Nat.add_le_add_left ?_ _)
  exact (SeparatedRank.rank_sum_le Finset.univ _).trans
    (Finset.sum_le_sum fun j _ => rank_entryProd _ _)

end Rank

section Registers

variable {J X K : Type*}

/-- These records are coefficient functions of affine expressions in the
distinct frontier placeholders. They may depend on the original input. -/
structure Form (J X K : Type*) where
  offset : X → K
  coeff : J → X → K

def Form.eval [Fintype J] [CommSemiring K] (f : Form J X K) (atom : J → X → K) (x : X) : K :=
  f.offset x + ∑ j, f.coeff j x * atom j x

/-- Indices point to earlier registers and may be used repeatedly. -/
inductive Gate (J X K : Type*) (n : ℕ)
  | source (j : J)
  | ambient (f : X → K)
  | add (i j : Fin n)
  | scale (a : X → K) (i : Fin n)

inductive Program (J X K : Type*) : ℕ → Type _
  | empty : Program J X K 0
  | push {n : ℕ} (prev : Program J X K n) (gate : Gate J X K n) : Program J X K (n+1)

variable [CommSemiring K]

def Gate.value {n : ℕ} (g : Gate J X K n) (old : Fin n → X → K) (atom : J → X → K) :
    X → K :=
  match g with
  | .source j => atom j
  | .ambient f => f
  | .add i j => fun x => old i x + old j x
  | .scale a i => fun x => a x * old i x

def Gate.form [DecidableEq J] {n : ℕ} (g : Gate J X K n)
    (old : Fin n → Form J X K) : Form J X K :=
  match g with
  | .source j => ⟨fun _ => 0, fun k _ => if k = j then 1 else 0⟩
  | .ambient f => ⟨f, fun _ _ => 0⟩
  | .add i j => ⟨fun x => (old i).offset x + (old j).offset x,
      fun k x => (old i).coeff k x + (old j).coeff k x⟩
  | .scale a i => ⟨fun x => a x * (old i).offset x,
      fun k x => a x * (old i).coeff k x⟩

def Program.values (atom : J → X → K) : {n : ℕ} → Program J X K n → Fin n → X → K
  | _, .empty => Fin.elim0
  | _, .push prev g => Fin.cases (g.value (prev.values atom) atom) (prev.values atom)

def Program.forms [DecidableEq J] : {n : ℕ} → Program J X K n → Fin n → Form J X K
  | _, .empty => Fin.elim0
  | _, .push prev g => Fin.cases (g.form prev.forms) prev.forms

variable [Fintype J] [DecidableEq J]

theorem Gate.form_eval {n : ℕ} (g : Gate J X K n) (old : Fin n → Form J X K)
    (atom : J → X → K) (x : X) :
    (g.form old).eval atom x = g.value (fun i => (old i).eval atom) atom x := by
  cases g with
  | source j => simp [Gate.form, Gate.value, Form.eval, ite_mul]
  | ambient f => simp [Gate.form, Gate.value, Form.eval]
  | add i j =>
    simp only [Gate.form, Gate.value, Form.eval, add_mul, Finset.sum_add_distrib]
    exact add_add_add_comm _ _ _ _
  | scale a i => simp only [Gate.form, Gate.value, Form.eval, mul_add, Finset.mul_sum, mul_assoc]

/-- Substituting all uses of shared source nodes gives one coefficient per
placeholder, independent of fan-out and of the number of directed paths. -/
theorem Program.evaluation {n : ℕ} (p : Program J X K n) (atom : J → X → K)
    (i : Fin n) (x : X) : (p.forms i).eval atom x = p.values atom i x := by
  induction p generalizing x with
  | empty => exact Fin.elim0 i
  | push prev g ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Program.forms, Program.values, Fin.cases_zero, Gate.form_eval]
      have h : (fun j => (prev.forms j).eval atom) = prev.values atom := by
        funext j y
        exact ih j y
      rw [h]
    · exact ih j x

end Registers

section Assembly

variable {R C J K : Type*} [Fintype R] [Fintype C] [Fintype J] [DecidableEq J] [Field K]

def mat (f : R × C → K) : Matrix R C K := Matrix.of fun r c => f (r,c)

/-- A cap on a concrete straight-line register evaluation. The coefficient
matrices in the conclusion are computed from the actual program. -/
theorem program_capacity {n : ℕ} (p : Program J (R × C) K n)
    (i : Fin n) (atom : J → R × C → K) :
    (mat (p.values atom i)).rank ≤
      (mat (p.forms i).offset).rank +
        ∑ j, (mat ((p.forms i).coeff j)).rank * (mat (atom j)).rank := by
  have h : mat (p.values atom i) = mat (p.forms i).offset +
      ∑ j, entryProd (mat ((p.forms i).coeff j)) (mat (atom j)) := by
    ext r c
    simpa [mat, Form.eval, Matrix.sum_apply, entryProd] using (p.evaluation atom i (r,c)).symm
  rw [h]
  exact affine_rank_budget _ _ _

end Assembly

section Mixed

variable {R C K U V : Type*} [Fintype R] [Fintype C] [Field K] [Fintype U] [Fintype V]

/-- Keep the actual ranks and the two unequal geometric deficits when
assembling the terminal rank test on one common matrix. -/
theorem two_route_budget (m dM dD : ℕ) (M : Matrix R C K)
    (main : U → Matrix R C K) (app : V → Matrix R C K) (w : U → ℕ) (v : V → ℕ)
    (hfull : M.rank = 2 ^ m) (hsum : M = (∑ i, main i) + ∑ j, app j)
    (hm : ∀ i, (main i).rank ≤ w i * 2 ^ (m - dM))
    (hd : ∀ j, (app j).rank ≤ v j * 2 ^ (m - dD)) :
    2 ^ m ≤ (∑ i, w i) * 2 ^ (m - dM) + (∑ j, v j) * 2 ^ (m - dD) := by
  rw [← hfull, hsum]
  refine (SeparatedRank.rank_add_le _ _).trans (Nat.add_le_add ?_ ?_)
  · rw [Finset.sum_mul]
    exact (SeparatedRank.rank_sum_le Finset.univ _).trans (Finset.sum_le_sum fun i _ => hm i)
  · rw [Finset.sum_mul]
    exact (SeparatedRank.rank_sum_le Finset.univ _).trans (Finset.sum_le_sum fun j _ => hd j)

/-- Rational normalization preserves each route's own deficit. -/
theorem normalized_two_route (m dM dD a b : ℕ) (hM : dM ≤ m) (hD : dD ≤ m)
    (h : 2 ^ m ≤ a * 2 ^ (m - dM) + b * 2 ^ (m - dD)) :
    (1 : ℚ) ≤ a / (2 : ℚ) ^ dM + b / (2 : ℚ) ^ dD := by
  have hq : (2 : ℚ)^m ≤ a * (2 : ℚ)^(m-dM) + b * (2 : ℚ)^(m-dD) := by exact_mod_cast h
  have portion (d t : ℕ) (hd : d ≤ m) :
      (t : ℚ) * (2 : ℚ) ^ (m-d) / (2 : ℚ) ^ m = t / (2 : ℚ) ^ d := by
    apply (div_eq_div_iff (by positivity) (by positivity)).2
    rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hd]
  calc
    (1 : ℚ) = (2 : ℚ)^m / (2 : ℚ)^m := (div_self (by positivity)).symm
    _ ≤ _ := div_le_div_of_nonneg_right hq (by positivity)
    _ = _ := by rw [add_div, portion _ _ hM, portion _ _ hD]

end Mixed

section Adaptive

variable {R C L K : Type*} [Fintype R] [Fintype C] [Fintype L] [DecidableEq L] [Field K]

def mask (route : R → C → L) (l : L) : Matrix R C K :=
  Matrix.of fun r c => if route r c = l then 1 else 0

/-- A routed affine register output expands using exactly one selected
guard per input. The cap counts the rank of each *guarded* transfer. -/
theorem routed_capacity {J : L → Type*} [∀ l, Fintype (J l)] (route : R → C → L)
    (bypass : L → Matrix R C K) (weights atoms : (l : L) → J l → Matrix R C K)
    (M : Matrix R C K) (hval : ∀ r c, let l := route r c
      M r c = bypass l r c + ∑ j, weights l j r c * atoms l j r c) :
    M.rank ≤ ∑ l, ((entryProd (mask route l) (bypass l)).rank +
      ∑ j, (entryProd (mask route l) (weights l j)).rank * (atoms l j).rank) := by
  classical
  let block (l : L) := entryProd (mask route l) (bypass l) +
    ∑ j, entryProd (entryProd (mask route l) (weights l j)) (atoms l j)
  have hsum : M = ∑ l, block l := by
    ext r c
    rw [Matrix.sum_apply, Finset.sum_eq_single (route r c)]
    · simpa [block, Matrix.add_apply, Matrix.sum_apply, entryProd, mask] using hval r c
    · intro l _ hl
      simp [block, Matrix.sum_apply, entryProd, mask, Ne.symm hl]
    · simp
  let cap (l : L) := (entryProd (mask route l) (bypass l)).rank +
    ∑ j, (entryProd (mask route l) (weights l j)).rank * (atoms l j).rank
  have hc (l : L) : (block l).rank ≤ cap l :=
    affine_rank_budget (entryProd (mask route l) (bypass l))
      (fun j => entryProd (mask route l) (weights l j)) (atoms l)
  calc
    M.rank = (∑ l, block l).rank := congrArg Matrix.rank hsum
    _ ≤ ∑ l, (block l).rank := SeparatedRank.rank_sum_le Finset.univ block
    _ ≤ ∑ l, cap l := Finset.sum_le_sum fun l _ => hc l

end Adaptive

section Costs

variable {X L J E : Type*}

/-- Kraft accounting on a genuinely realized input. Empty transcripts
must have zero contribution. The two resources belong to the same leaf. -/
theorem realized_kraft [Fintype L] [Nonempty L] (route : X → L)
    (bits : L → ℕ) (mass : L → ℚ)
    (hbudget : 1 ≤ ∑ l, mass l) (hkraft : (∑ l, 1 / (2 : ℚ)^(bits l)) ≤ 1)
    (hzero : ∀ l, (¬ ∃ x, route x = l) → mass l = 0) :
    ∃ x, 1 ≤ (2 : ℚ) ^ (bits (route x)) * mass (route x) := by
  classical
  by_contra! hn
  have hlt (l : L) : mass l < 1 / (2 : ℚ)^(bits l) := by
    by_cases hit : ∃ x, route x = l
    · obtain ⟨x, rfl⟩ := hit
      exact (lt_div_iff₀ (by positivity)).2 (by simpa only [mul_comm] using hn x)
    · rw [hzero l hit]
      exact div_pos zero_lt_one (pow_pos (by norm_num) _)
  exact (not_lt_of_ge (hkraft.trans hbudget))
    (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun l _ => hlt l)

open GuardedBarrier in
/-- Identity for the actual finite binary tree. An unreachable leaf still
has a codeword and must have zero rank contribution in realized_kraft. -/
theorem tree_kraft (tree : QueryTree X) :
    (∑ l : tree.Leaf, 1 / (2 : ℚ) ^ (tree.path l).length) = 1 := by
  induction tree with
  | stop => simp [QueryTree.Leaf, QueryTree.path]
  | query test no yes hn hy =>
    change (∑ l : no.Leaf ⊕ yes.Leaf, _) = _
    rw [Fintype.sum_sum_type]
    simp only [QueryTree.path, List.length_cons, pow_succ, div_mul_eq_div_div]
    have avg {I : Type} [Fintype I] (f : I → ℚ) :
        (∑ i, f i / 2) = (∑ i, f i) / 2 := by
      simp only [div_eq_mul_inv, Finset.sum_mul]
    rw [avg (fun x : no.Leaf => 1 / (2 : ℚ)^(no.path x).length),
      avg (fun x : yes.Leaf => 1 / (2 : ℚ)^(yes.path x).length), hn, hy]
    norm_num

/-- Finite batched events cover distinct frontier values. A repeated value
can be present in multiple events. -/
theorem covered_batches [Fintype J] [DecidableEq J] [Fintype E]
    (out : E → Finset J) (cost : E → ℕ) (W : ℕ)
    (cover : ∀ j, ∃ e, j ∈ out e) (rate : ∀ e, (out e).card ≤ W * cost e) :
    Fintype.card J ≤ W * ∑ e, cost e := by
  classical
  have hall : Finset.univ.biUnion out = Finset.univ := by
    ext j
    simp [cover j]
  calc
    Fintype.card J = (Finset.univ.biUnion out).card := by rw [hall, Finset.card_univ]
    _ ≤ ∑ e, (out e).card := Finset.card_biUnion_le
    _ ≤ ∑ e, W * cost e := Finset.sum_le_sum fun e _ => rate e
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- An integrated bound on one realized run from normalized guarded
mass and the coverage/rate bound on that run. -/
theorem realized_cost [Fintype L] [Nonempty L] (route : X → L)
    (bits work : L → ℕ) (mass : L → ℚ) (d W ρ : ℕ)
    (hbudget : 1 ≤ ∑ l, mass l) (hkraft : (∑ l, 1 / (2 : ℚ)^(bits l)) ≤ 1)
    (hzero : ∀ l, (¬ ∃ x, route x = l) → mass l = 0)
    (hcharge : ∀ l, mass l ≤ (ρ : ℚ) * W * work l / (2 : ℚ)^d) :
    ∃ x, 2^d ≤ 2^(bits (route x)) * ρ * W * work (route x) := by
  obtain ⟨x, hx⟩ := realized_kraft route bits mass hbudget hkraft hzero
  refine ⟨x, ?_⟩
  have ht := hx.trans (mul_le_mul_of_nonneg_left (hcharge (route x)) (by positivity))
  rw [← mul_div_assoc] at ht
  have hp := (le_div_iff₀ (by positivity)).mp ht
  simp only [one_mul] at hp
  exact_mod_cast (by simpa only [mul_assoc] using hp :
    (2 : ℚ)^d ≤ (2 : ℚ)^(bits (route x)) * ρ * W * work (route x))

end Costs

#print axioms exact_factorization
#print axioms rank_entryProd
#print axioms affine_rank_budget
#print axioms Gate.form_eval
#print axioms Program.evaluation
#print axioms program_capacity
#print axioms two_route_budget
#print axioms normalized_two_route
#print axioms routed_capacity
#print axioms realized_kraft
#print axioms tree_kraft
#print axioms covered_batches
#print axioms realized_cost

end HybridFrontier
