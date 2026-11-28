import V8CapacityUnifiedScalarWeights

/-! Exact finite indexing of S2. The cardinality is that of all
nonnegative exponent tuples with the printed strict budget; the
auxiliary finite bound creates no additional filter. -/
namespace V8CapacityUnified.Scalar
open scoped Classical BigOperators
open V8CapacityFactorial V8CapacityMonicBasis V8CapacityGridOrder

noncomputable section
set_option linter.unusedSectionVars false

variable {H : Type*} [Fintype H]

def auxiliaryDegree (H : Type*) [Fintype H] (q P : ℕ) :=
  Fintype.card H * (P*q-1)

abbrev S2Index (q P : ℕ) (v : H → ℕ) :=
  {a : Row H (auxiliaryDegree H q P) // weight q v (rowDegree a)<P}

abbrev S2Raw (q P : ℕ) (v : H → ℕ) :=
  {a : H → ℕ // weight q v a<P}

def indexDegree {q P : ℕ} {v : H → ℕ} (i : S2Index q P v) : H → ℕ :=
  rowDegree i.val

theorem div_le_debt (q n : ℕ) : n/q≤debt q n := by
  unfold debt
  have h := Finset.single_le_sum (f:=fun u : ℕ => n/q^(u+1))
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (show 0<n+1 by omega))
  simpa using h

theorem order_cost_bound (q P : ℕ) (hq : 0<q) (v a : H → ℕ)
    (ha : weight q v a<P) (i : H) :
    a i<P*q := by
  have hi : v i*a i+debt q (a i)≤weight q v a :=
    Finset.single_le_sum (f:=fun i => v i*a i+debt q (a i)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hdiv : a i/q<P := (div_le_debt q (a i)).trans_lt ((Nat.le_add_left _ _).trans_lt (hi.trans_lt ha))
  exact (Nat.div_lt_iff_lt_mul hq).mp hdiv

theorem active_total_bound (q P : ℕ) (hq : 0<q) (v a : H → ℕ)
    (ha : weight q v a<P) :
    (∑ i : H, a i)≤auxiliaryDegree H q P := by
  calc
    _ ≤ ∑ _ : H, (P*q-1) := Finset.sum_le_sum (fun i _ => by
      have h := order_cost_bound q P hq v a ha i
      omega)
    _ = _ := by simp [auxiliaryDegree]

theorem row_bound (a : H → ℕ) (D : ℕ) (ha : (∑ i : H, a i)≤D) (i : H) : a i<D+1 :=
  Nat.lt_succ_of_le ((Finset.single_le_sum (f:=a) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ i)).trans ha)

def exactS2Index (q P : ℕ) (hq : 0<q) (v : H → ℕ) : S2Index q P v ≃ S2Raw q P v where
  toFun a := ⟨indexDegree a,a.property⟩
  invFun a :=
    let ht := active_total_bound q P hq v a.val a.property
    ⟨⟨fun i => ⟨a.val i,row_bound a.val (auxiliaryDegree H q P) ht i⟩,ht⟩,a.property⟩
  left_inv a := by apply Subtype.ext; apply Subtype.ext; funext i; exact Fin.ext rfl
  right_inv _ := rfl

theorem s2_is_exact_count (q P : ℕ) (hq : 0<q) (v : H → ℕ) :
    Fintype.card (S2Index q P v)=Nat.card (S2Raw q P v) := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (exactS2Index q P hq v)

def indexFor (q P : ℕ) (hq : 0<q) (v a : H → ℕ) (h : weight q v a<P) :
    S2Index q P v := (exactS2Index q P hq v).symm ⟨a,h⟩

theorem indexFor_degree (q P : ℕ) (hq : 0<q) (v a : H → ℕ) (h : weight q v a<P) :
    indexDegree (indexFor q P hq v a h)=a :=
  congrArg Subtype.val ((exactS2Index q P hq v).apply_symm_apply ⟨a,h⟩)

def indexOrder (q P : ℕ) (v : H → ℕ) : LinearOrder (S2Index q P v) :=
  letI : LinearOrder (Row H (auxiliaryDegree H q P)) := gridOrder
  inferInstance

theorem index_order_le {q P : ℕ} {v : H → ℕ} (x y : S2Index q P v)
    (h : ∀ i, indexDegree x i ≤ indexDegree y i) :
    @LE.le _ (indexOrder q P v).toLE x y :=
  coordinate_le h

#print axioms div_le_debt
#print axioms active_total_bound
#print axioms exactS2Index
#print axioms s2_is_exact_count
#print axioms indexFor_degree
#print axioms index_order_le
end
end V8CapacityUnified.Scalar
