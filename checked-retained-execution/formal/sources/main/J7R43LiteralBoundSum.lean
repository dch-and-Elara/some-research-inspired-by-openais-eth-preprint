import J7R43LiteralBoundRows

/-! The real zero-probe group values fit at the printed precision.
This bounds the unchanged individual child, not a divided or
completed register, and applies equally to the zero-mode baseline. -/
namespace J7R43Literal
open scoped BigOperators Classical
open J8Physical J8J9Grouped J6R14SpecializedBox
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type} {P : V→Type} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
variable (e : EndpointSeating d) (even : Even L)
variable (F : OldTables d) (sign : S→Bool)

theorem local_assignment_count (idx : Wire R≃Fin M) (g : G) :
    Fintype.card (Assignment d g) ≤ 2^M := by
  let em (x : Assignment d g) := cubeEquiv d idx (onlyGroup d g x)
  have em_inj : Function.Injective em := by
    intro x y h
    have h' := congrFun ((cubeEquiv d idx).injective h) g
    simpa only [onlyGroup_here] using h'
  simpa using Fintype.card_le_of_injective em em_inj

private theorem truth_nonneg {U : Type*} (tab : LiteralPortCompiler.CNF U) (x : U→Bool) :
    0≤(LiteralPortCompiler.truth tab x : ℤ) := by
  unfold LiteralPortCompiler.truth LiteralPortCompiler.indicator
  cases LiteralPortCompiler.satisfied tab x <;> norm_num

theorem local_table_range (g : G) (x : Assignment d g) :
    0≤ tablesAt d F sign g x ∧ tablesAt d F sign g x ≤ 1 := by
  unfold tablesAt table
  let uv := ∏ i : LocalPin d g, (LiteralPortCompiler.truth
    (LiteralPortCompiler.pin i (sign i.val)) x.1 : ℤ)
  let wd := ∏ v : LocalColumn d g, (LiteralPortCompiler.truth (F g v) (x.2 v) : ℤ)
  have h₀ : 0≤uv := Finset.prod_nonneg (fun i _ => truth_nonneg _ _)
  have h₁ : 0≤wd := Finset.prod_nonneg (fun v _ => truth_nonneg _ _)
  have huv : uv≤1 := by
    have h (i : LocalPin d g) : (LiteralPortCompiler.truth
        (LiteralPortCompiler.pin i (sign i.val)) x.1 : ℤ) ≤ 1 := le_abs_self _ |>.trans (truth_abs _ _)
    simpa only [Finset.prod_const_one] using Finset.prod_le_prod (g := fun _ => (1:ℤ))
      (fun i _ => truth_nonneg _ _) (fun i _ => h i)
  have hwd : wd≤1 := by
    have h (v : LocalColumn d g) : (LiteralPortCompiler.truth (F g v) (x.2 v) : ℤ) ≤ 1 :=
      (le_abs_self _).trans (truth_abs _ _)
    simpa only [Finset.prod_const_one] using Finset.prod_le_prod (g := fun _ => (1:ℤ))
      (fun v _ => truth_nonneg _ _) (fun v _ => h v)
  exact ⟨mul_nonneg h₀ h₁,mul_le_one₀ huv h₁ hwd⟩

theorem nonneg_tile_feature (s : S) (b : Fin (Fintype.card (PinTile d s)))
    (x : Assignment d (d.pinLabel s)) : 0≤feature d s b x := by
  unfold feature
  have hb (t : Bool) : 0≤J8J9Grouped.bit t := by cases t <;> decide
  exact add_nonneg (Finset.sum_nonneg fun _ _ => mul_nonneg (by positivity) (hb _))
    (Finset.sum_nonneg fun _ _ => mul_nonneg (hb _) (by positivity))

set_option maxHeartbeats 1800000 in
include even in
theorem source_feature_range (s : S) (idx : Wire R≃Fin M) (hL : 3≤L) (hM : L^3≤M)
    (b : Fin (Fintype.card (PinTile d s))) (x : Assignment d (d.pinLabel s)) :
    0≤feature d s b x ∧ feature d s b x≤(2:ℤ)^M := by
  have h0 := nonneg_tile_feature d s b x
  have h := cubeFeature_bound d s b idx (onlyGroup d (d.pinLabel s) x) hL
  rw [onlyGroup_here,abs_of_nonneg h0] at h
  have hB : b.val+1≤L := by
    have hb := b.isLt
    have hn := pins_per_tile d s even
    omega
  have hX : (b.val+1)*L ≤ M := by
    refine (Nat.mul_le_mul_right L hB).trans ?_
    calc
      L*L = L^2 := (pow_two L).symm
      _ ≤ L^3 := Nat.pow_le_pow_right (by omega) (by decide)
      _ ≤ _ := hM
  exact ⟨h0,h.trans (pow_le_pow_right₀ (by decide) hX)⟩

set_option maxHeartbeats 2500000 in
theorem literal_group_feature_range (s : S) (idx : Wire R≃Fin M) (hL : 1≤L)
    (capacity : L*Fintype.card Packet≤3*M)
    (g : G) (feat : Assignment d g→ℤ)
    (hfeat : ∀ x, 0≤feat x ∧ feat x≤(2:ℤ)^M) :
    let N := J8J9Grouped.child d e even F sign g none feat
    0≤N ∧ N≤(2:ℤ)^(8*M) := by
  rw [child_as_sum]
  have bounded (x : Assignment d g) :
      0≤summand d e even F sign g none feat x ∧
        summand d e even F sign g none feat x ≤ (2:ℤ)^(7*M) := by
    have targ := literal_group_row_bounds d e even s idx hL capacity g x
    have p0 : 0≤∏ r : LocalRow d g, exactBaselineRow d e even g x r :=
      Finset.prod_nonneg (fun r _ => le_trans (by norm_num) (targ.1 r))
    have t0 := local_table_range d F sign g x
    have f0 := hfeat x
    change 0≤tablesAt d F sign g x * feat x * (∏ r, exactBaselineRow d e even g x r) ∧ _
    constructor
    · exact mul_nonneg (mul_nonneg t0.1 f0.1) p0
    · change tablesAt d F sign g x * feat x * (∏ r, exactBaselineRow d e even g x r) ≤ _
      have hb : tablesAt d F sign g x * feat x ≤ (2:ℤ)^M :=
        (mul_le_of_le_one_left f0.1 t0.2).trans f0.2
      calc
        _ ≤ (2:ℤ)^M * (2:ℤ)^(6*M) := mul_le_mul hb targ.2 p0 (by positivity)
        _ = _ := by rw [← pow_add]; congr 1; omega
  constructor
  · exact Finset.sum_nonneg (fun x _ => (bounded x).1)
  · calc
      _ ≤ ∑ _ : Assignment d g, (2:ℤ)^(7*M) := Finset.sum_le_sum fun x _ => (bounded x).2
      _ = (Fintype.card (Assignment d g) : ℤ)*(2:ℤ)^(7*M) := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      _ ≤ (2:ℤ)^M*(2:ℤ)^(7*M) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact_mod_cast local_assignment_count d idx g
      _ = _ := by rw [← pow_add]; congr 1; omega

private theorem within_native (n : ℤ) (M p : ℕ) (hM : 0<M) (hp : 10*M≤p)
    (hfit : 0≤n ∧ n≤(2:ℤ)^(8*M)) :
    0≤n ∧ n.toNat < 2^p := by
  refine ⟨hfit.1,?_⟩
  have ht : n<(2:ℤ)^p := hfit.2.trans_lt (pow_lt_pow_right₀ (by norm_num) (by omega))
  have hn : (n.toNat:ℤ)=n := Int.toNat_of_nonneg hfit.1
  rw [← hn] at ht
  exact_mod_cast ht

theorem literal_native_source_fits (s : S) (idx : Wire R≃Fin M) (hL : 3≤L) (hM : L^3≤M)
    (capacity : L*Fintype.card Packet≤3*M) (b : Fin (Fintype.card (PinTile d s)))
    (p : ℕ) (hp : 10*M≤p) :
    let N := J8J9Grouped.child d e even F sign (d.pinLabel s) none (feature d s b)
    0≤N ∧ N.toNat<2^p := by
  dsimp only
  have hM' : 0<M := (pow_pos (by omega : 0<L) 3).trans_le hM
  refine within_native _ M p hM' hp ?_
  exact literal_group_feature_range d e even F sign s idx (by omega) capacity _
    (feature d s b) (source_feature_range d even s idx hL hM b)

theorem literal_native_baseline_fits (s : S) (idx : Wire R≃Fin M) (hL : 1≤L) (hM : 0<M)
    (capacity : L*Fintype.card Packet≤3*M) (g : G) (p : ℕ) (hp : 10*M≤p) :
    let N := J8J9Grouped.child d e even F sign g none (fun _ => 1)
    0≤N ∧ N.toNat<2^p := by
  dsimp only
  apply within_native _ M p hM hp
  exact literal_group_feature_range d e even F sign s idx hL capacity g _
    (fun _ => ⟨by norm_num,one_le_pow₀ (by norm_num)⟩)

#print axioms local_assignment_count
#print axioms local_table_range
#print axioms source_feature_range
#print axioms literal_group_feature_range
#print axioms literal_native_source_fits
#print axioms literal_native_baseline_fits
end
end J7R43Literal