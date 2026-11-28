import V8NativeMessageN7LiteralSupportFlat
import V8NativeMessageN7HighBoundInteger
import V8NativeMessageN7HighBoundFinite
import V8NativeMessageN7HighBoundReceipt

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15000000
set_option maxRecDepth 2100

/-! A short independent height check using the same two Boolean cubes
appearing in the source's odd-shift argument. This also proves the
printed bound at the unit shift, without any row-elimination premise. -/
namespace V8NativeMessage.N7HighBound
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
  J6R9PacketTiles V8NativeMessage.N7LiteralSupport

noncomputable section

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
  [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G)

omit [Fintype A] [Fintype B] in
theorem actual_unit_shift_argument (w : Port E→Bool) (r : E) :
    ∃ ok : Bool, (-1:ℤ)*wholeShiftBit P ℤ (-1) w r=if ok then -1 else 0 := by
  by_cases matchCol : ∃ q,Matches P (-1) r q
  · obtain ⟨q,hit⟩ := matchCol
    refine ⟨w (.inr q),?_⟩
    rw [literal_port_bit_unique P (-1) w r q hit]
    cases w (.inr q) <;> norm_num [bit]
  · refine ⟨false,?_⟩
    rw [literal_unmatched_port_zero P (-1) w r (fun q h=>matchCol ⟨q,h⟩)]
    norm_num

omit [Fintype A] [Fintype B] in
theorem actual_unit_affine_bound (w : Port E→Bool) (r : E) :
    |LiteralPortCompiler.affine (w (.inl r)) ((-1:ℤ)*wholeShiftBit P ℤ (-1) w r)| ≤ 2 := by
  obtain ⟨ok,h⟩ := actual_unit_shift_argument P w r
  rw [h]
  cases ok <;> cases w (.inl r) <;> norm_num [LiteralPortCompiler.affine]

variable (flags : ∀ v : A⊕B,(ParentPorts N v→Bool)→Bool)

theorem actual_unit_flat_term_height (w : Port E→Bool) :
    |flatTerm P (-1) (-1:ℤ) flags w| ≤ (2:ℤ)^Fintype.card E := by
  let u (v : A⊕B) : ℤ := bit ℤ (flags v (fun q=>w q.val))
  let t (r : E) := LiteralPortCompiler.affine (w (.inl r))
    ((-1:ℤ)*wholeShiftBit P ℤ (-1) w r)
  change |(∏ v,u v)*(∏ r,t r)|≤_
  have hU : |∏ v,u v|≤1 := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _v : A⊕B,(1:ℤ) := Finset.prod_le_prod
        (fun _ _=>abs_nonneg _) (fun v _=>by
          unfold u
          cases flags v (fun q=>w q.val) <;> norm_num [bit])
      _ = _ := by simp
  have hT : |∏ r,t r|≤(2:ℤ)^Fintype.card E := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _r : E,(2:ℤ) := Finset.prod_le_prod
        (fun _ _=>abs_nonneg _) (fun r _=>actual_unit_affine_bound P w r)
      _ = _ := by simp
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul hU hT (abs_nonneg _) (by norm_num : (0:ℤ)≤1)

theorem true_unit_integer_height (i : Fin a) (hv : padicValInt 2 (-1)=i.val) :
    |unitInteger P i flags|≤(8:ℤ)^Fintype.card E := by
  let M := Fintype.card E
  have eq : unitInteger P i flags=flatSigned P (-1) (-1:ℤ) flags :=
    full_root_at_zero_has_literal_two_cubes P i (by norm_num) hv (-1:ℤ) flags
  rw [eq]
  unfold flatSigned
  have hCube : Fintype.card (Port E→Bool) = 2^(2*M) := by
    simp [Port,M,two_mul]
  calc
    _ ≤ ∑ w : Port E→Bool,|flatTerm P (-1) (-1:ℤ) flags w| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _w : Port E→Bool,(2:ℤ)^M :=
      Finset.sum_le_sum (fun w _=>actual_unit_flat_term_height P flags w)
    _ = (2:ℤ)^(2*M)*(2:ℤ)^M := by
      simp only [Finset.sum_const,Finset.card_univ,hCube,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    _ = (8:ℤ)^M := by
      rw [pow_mul,←mul_pow]
      norm_num

theorem true_unit_printed_height (i : Fin a) (hv : padicValInt 2 (-1)=i.val) :
    |unitInteger P i flags|≤(2:ℤ)^Fintype.card E*7^Fintype.card E := by
  calc
    _ ≤ (8:ℤ)^Fintype.card E := true_unit_integer_height P flags i hv
    _ ≤ (14:ℤ)^Fintype.card E := pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = _ := by rw [←mul_pow]; norm_num

variable {f : ℤ[X]}

theorem true_unit_intcast_window
    (i : Fin a) (hv : padicValInt 2 (-1)=i.val) (hM : 0<Fintype.card E)
    (p : ℕ) (hp : 4*Fintype.card E<p) (hf : f.Monic) (hd : 0<f.natDegree) :
    let Z := unitInteger P i flags
    let v := (Z:Box f 1 p)
    |Z|≤(2:ℤ)^Fintype.card E*7^Fintype.card E ∧
    centeredBox p f hf v=Z ∧ (v=0 ↔ exactZero P i (-1) flags=0) := by
  let Z := unitInteger P i flags
  have bound : |Z|≤(2:ℤ)^Fintype.card E*7^Fintype.card E :=
    true_unit_printed_height P flags i hv
  have fit : 2*|Z|<(2:ℤ)^p := unit_centered_window hM hp bound
  have small : |Z|<(2:ℤ)^p := by linarith only [fit,abs_nonneg Z]
  have pp : 0<p := by omega
  exact ⟨bound,centered_box_recovers p pp f hf hd Z fit,
    (integer_box_zero_iff_of_height p pp f hf hd Z small).trans
      (exact_unit_zero_iff P i flags).symm⟩

theorem true_unit_native_slot_window
    (i : Fin a) (hv : padicValInt 2 (-1)=i.val) (hM : 0<Fintype.card E)
    (p₀ p : ℕ) (hp₀ : 0<p₀) (hp : 4*Fintype.card E<p) (hf : f.Monic) (hd : 0<f.natDegree) :
    let Z := unitInteger P i flags
    let v := nativeUnitZeroSlot P i flags hv p₀ p hf
    |Z|≤(2:ℤ)^Fintype.card E*7^Fintype.card E ∧
    centeredBox p f hf v=Z ∧ (v=0 ↔ exactZero P i (-1) flags=0) := by
  dsimp only
  rw [actual_unit_slot_is_integer P i flags hv p₀ p hp₀ hf hd]
  exact true_unit_intcast_window P flags i hv hM p hp hf hd

#print axioms actual_unit_shift_argument
#print axioms actual_unit_affine_bound
#print axioms actual_unit_flat_term_height
#print axioms true_unit_integer_height
#print axioms true_unit_printed_height
#print axioms true_unit_intcast_window
#print axioms true_unit_native_slot_window
end
end V8NativeMessage.N7HighBound
