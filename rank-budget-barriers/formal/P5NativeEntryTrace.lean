import P5NativeEntryBranch
import P5NativeEntryTuning
import P5MainIteratorSource
import P5MainIteratorChoose

/-! Cost transfer for the named rational execution, not for an arbitrary
algorithm computing the same count.  An embedding into `Fin T` records
different actually charged events of one execution.  The reference
loops require these events; an implicit enumeration does not. -/
namespace Paper5.NativeEntry
open scoped BigOperators Classical
open P5MainIterator

abbrev ExhaustiveReceipt (n T : ℕ) := ((Fin n → Bool) ↪ Fin T)

theorem exhaustive_log_cost {n T : ℕ} (w : ExhaustiveReceipt n T) :
    (n:ℝ)≤logTwo T := by
  apply binary_exponent_le T n
  simpa only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using
    Fintype.card_le_of_injective w w.injective

abbrev BranchLayout {n : ℕ} (A : Rows n) (copies : ℕ) :=
  SourceLayout (Ports A) (Free A) (Factors A) (Fin copies)
    (Fin (printedNodes (dim A))) (Fin (printedGroups (dim A)))

theorem zero_tuple_reached {n copies : ℕ} {A : Rows n} (keep : ℕ→Prop)
    (L : BranchLayout A copies) (t : Fin (printedNodes (dim A))) :
    sourceTuple keep L t (fun _=>false)=0 := by
  funext g
  have h : (fun v : Free A => if L.a v t=g then BooleanMeasurement.bit ℚ false else 0)=0 := by
    funext v
    simp [BooleanMeasurement.bit]
  rw [sourceTuple,h,Matrix.mulVec_zero]
  rfl

abbrev PrintedGroup {n copies : ℕ} {A : Rows n}
    (L : BranchLayout A copies) (t : Fin (printedNodes (dim A))) :=
  fun v : Free A=>L.a v t

abbrev ScanSlots {n copies : ℕ} {A : Rows n}
    (L : BranchLayout A copies) (t : Fin (printedNodes (dim A))) :=
  Σ g : Fin (printedGroups (dim A)), ({v : Free A // L.a v t=g} → Bool)

theorem scan_slot_uses_each_assignment {n copies : ℕ} {A : Rows n}
    (L : BranchLayout A copies) (t : Fin (printedNodes (dim A)))
    (g : Fin (printedGroups (dim A))) (x : {v : Free A // L.a v t=g} → Bool) :
    Sigma.mk g x ∈ (Finset.univ : Finset (ScanSlots L t)).toList := by
  simp

/-- At the empty Taylor pair, the all-zero tuple is feasible.  The printed
second scan at that tuple processes all local assignments, including
those not in the fiber.  `paid` is a receipt from that repeated loop. -/
structure PrintedScan {n : ℕ} (A : Rows n) (T : ℕ) where
  copies : ℕ
  layout : BranchLayout A copies
  actualOwner : ∀ e,layout.placement.owner e=portOwner e
  actualFactor : ∀ e,layout.factor e=portFactor e
  node : Fin (printedNodes (dim A))
  rGuard : 2≤printedGroups (dim A)
  paid : ScanSlots layout node ↪ Fin T

theorem printed_scan_group_cost {n T : ℕ} {A : Rows n} (P : PrintedScan A T) :
    (dim A:ℝ)/(printedGroups (dim A):ℝ)≤logTwo T := by
  have hG : Nonempty (Fin (printedGroups (dim A))) :=
    ⟨⟨0,by have h := P.rGuard; omega⟩⟩
  letI := hG
  obtain ⟨g,_,hm⟩ := largest_group_at_least_average (PrintedGroup P.layout P.node)
  let d := Fintype.card {v : Free A // P.layout.a v P.node=g}
  have hm' : dim A≤printedGroups (dim A)*d := by
    simp only [PrintedGroup,←Nat.card_eq_fintype_card] at hm
    have hFree : Nat.card (Free A)=dim A := by rw [Nat.card_eq_fintype_card,free_card]
    have hFin : Nat.card (Fin (printedGroups (dim A)))=printedGroups (dim A) := by simp
    rw [hFree,hFin] at hm
    simpa only [d,←Nat.card_eq_fintype_card] using hm
  have hinj : Function.Injective
      (fun x : {v : Free A // P.layout.a v P.node=g} → Bool => P.paid ⟨g,x⟩) := by
    intro x y h
    simpa using P.paid.injective h
  have hcard := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at hcard
  change 2^d≤T at hcard
  have hr : 0<(printedGroups (dim A):ℝ) := by
    exact_mod_cast (show 0<printedGroups (dim A) by have hh:=P.rGuard; omega)
  have hd : (dim A:ℝ)/(printedGroups (dim A):ℝ)≤(d:ℝ) := by
    apply (div_le_iff₀ hr).mpr
    rw [mul_comm]
    exact_mod_cast hm'
  exact hd.trans (binary_exponent_le T d hcard)

theorem printed_scan_full_scale {n T : ℕ} {A : Rows n} (hn : 20≤n) (P : PrintedScan A T) :
    binaryScale n/16≤logTwo T := by
  have h₁ := binary_le_two_rounded (n:=n) (by omega)
  have hN := dim_add_fixed A
  have hD := dim_at_least_half A hn
  have h₂ := rounded_half_comparison (d:=dim A) (n:=n) (by omega) (by omega) hD
  have h₃ := roundedScale_le_group_cost (n:=dim A) (by omega)
    (by have h := P.rGuard; omega)
  have h₄ := printed_scan_group_cost P
  linarith only [h₁,h₂,h₃,h₄]

/-- Cheap termination at this branch means no nonconstant rows remain.
On a signed-unit query the correctly set pins can never create a
contradictory constant, and full column rank excludes this cheap case. -/
inductive SparseCallReceipt {n : ℕ} (A : Rows n) (T : ℕ) where
  | trivial : (retained A).card=0 → SparseCallReceipt A T
  | fallback : ExhaustiveReceipt n T → SparseCallReceipt A T
  | printed : PrintedScan A T → SparseCallReceipt A T

/-- Source dispatch: preliminary exhaustive search, or one unchanged
nonempty signed-unit leaf.  Every list candidate of every fixed greedy
round is evaluated, including duplicate rows and all discarded lists. -/
inductive RationalEntryReceipt {n : ℕ} (sgn : Fin n→Bool) (T : ℕ) where
  | preliminary : printedGroups n<2 → ExhaustiveReceipt n T →
      RationalEntryReceipt sgn T
  | leaf (B : ℕ) (A₀ : Rows n) : 0<B → A₀.length≤3*n →
      (∀ r∈A₀,(support r).card≤hashD₀ n B) →
      (run : @Greedy n (hashP n B) sgn A₀) →
      (∀ j : Fin (3*n),∀ γ : Candidate n (hashP n B),
        SparseCallReceipt (run.rows j++[candidateRow γ]) T) →
      RationalEntryReceipt sgn T

theorem rational_entry_reached_paid {n T : ℕ} {sgn : Fin n→Bool}
    (hn : 20≤n) (trace : RationalEntryReceipt sgn T) :
    min (n:ℝ) (binaryScale n/16)≤logTwo T := by
  cases trace with
  | preliminary h x =>
      exact (min_le_left _ _).trans (exhaustive_log_cost x)
  | leaf B A₀ hB hInit hW run coverage =>
      obtain ⟨j,hj,γ,hA⟩ := first_full_rank_query_reached run
        (actual_params (n:=n) hB).1 (by omega)
      let A := run.rows j++[candidateRow γ]
      have hf : (matrix A).rank=n := hA
      have htest := branch_has_equations A hn hf
      cases coverage ⟨j,hj⟩ γ with
      | trivial hz =>
          change (retained A).card=0 at hz
          omega
      | fallback x =>
          exact (min_le_left _ _).trans (exhaustive_log_cost x)
      | printed w =>
          exact (min_le_right _ _).trans (printed_scan_full_scale hn w)

#print axioms exhaustive_log_cost
#print axioms zero_tuple_reached
#print axioms scan_slot_uses_each_assignment
#print axioms printed_scan_group_cost
#print axioms printed_scan_full_scale
#print axioms rational_entry_reached_paid
end Paper5.NativeEntry