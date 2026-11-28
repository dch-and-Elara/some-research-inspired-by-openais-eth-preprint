import P6JointLiteral
import P6JointMatching
import P6JointNumeric
import J7R13Root

namespace Paper6JointSeating
open scoped Classical BigOperators
open P11FullPacking P9BalancedChart
open J7SourceLabels J7SeatSource J7PrintedParamsGraph J9R20SameFile
open J7PrintedParams J7SourceConditioning J7FullWordCells J7FullWordAssembly
open J7SeatRounded J7SeatCertificate J7SeatQuota J7ToJ8Degree J7R13 J7ToJ8Canonical

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
local instance (priority := 100000) : DecidableEq Slot :=
  fun _ _ => Classical.propDecidable _
local instance (priority := 100000) {P R C : Type*} : DecidableEq (Block P R C) :=
  fun _ _ => Classical.propDecidable _

variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool ≃ Pin Pair×Fin 3)
local notation "W" => Wires Pair H
local notation "R" => OrdinaryRow Pair H
local notation "V" => OldNonPrivate Pair H
local notation "E" => Clones Pair
local notation "A" => Fin 64
local notation "N" => Fintype.card (Pin Pair)
local notation "M" => Fintype.card W
local notation "T" => rootT (sourceSize N)
local notation "L" => printedL T
local notation "C" => printedD T
local notation "Δ" => rootDelta (sourceSize N)
local notation "COL" => column ends cycle
local notation "B" => ((2*(Fintype.card E:ℝ)+9*(M:ℝ))/(2^(T+1):ℕ))
local notation "WORD" => State A (Fin T → A) Pair R V
local notation "CELL" => Cell (Fin (T+1)) A

/-- Exact printed labels and rounded maximum; no pre-supplied matching or
guarded order. Both guards and the relaxed recovery endpoints exist on one
physical seat chart. -/
theorem literalJointPrintedSeats
    (large : 2^(9*131072-1) < sourceSize N) :
    ∃ z : WORD,
      let label := wordLabel Prod.fst COL z
      let b := ceilCopies (2^(T+1)) (realMaximum label)
      J6R10Repack.varianceScore (J6R10Repack.declaredCell (network Prod.fst COL) (rowFull z) (colFull z)) ≤
        2*(Nat.card W:ℚ)*Δ ∧
      Nat.card (Page (T+1) b A)*2^(T+1) ≤ 3*Nat.card W ∧
      (∀ p : Pin Pair, (label (pinEmbed Pair (OrdinaryWire Pair H) p) 0).1 ≠
        (label (pinEmbed Pair (OrdinaryWire Pair H) p) 0).2) ∧
      ∃ (seat : W ↪ Physical (T+1) b A) (keep : Bool → Finset E),
        Disjoint (keep false) (keep true) ∧
        (∀ s, (Fintype.card E : ℝ)/(2^(T+1):ℕ) ≤ (keep s).card +
          Real.sqrt B + Real.sqrt ((Fintype.card CELL : ℝ)*B)) ∧
        (∀ w, physicalCell (balancedMask (T+1) b A) (seat w) = label w) ∧
        (∀ w s e, colNode COL w = .inr (cloneOwner e) → e ∈ keep s →
          (seat w).2 = endpointIndex (T+1) s) ∧
        (∀ w s, (seat w).2 = endpointIndex (T+1) s → nonpin COL w) ∧
        Set.InjOn (rowNode Prod.fst) {w | (seat w).2 = endpointIndex (T+1) false} := by
  classical
  have hM : M=24*N := (actual_incidence ends).1
  have hA : Fintype.card A=64 := by simp
  obtain ⟨hL,p1,p2,p3⟩ := four_clone_root_packing N (actual_incidence ends).2 large
  have hmargin := J7PrintedParams.margin N C L Δ (printedD_pos T) hL p1 p2 p3
  let ref : Seed A (Fin T → A) := ((0,(0,0),(0,0)),fun _ _ => 0)
  let reference : WORD := fun _ => ref
  have hrow (r : R) : (Finset.univ.filter fun w : OrdinaryWire Pair H => w.1=r).card ≤ 2 := by
    rw [← Fintype.card_subtype,← Nat.card_eq_fintype_card,ordinary_row_exact_two]
  obtain ⟨z,hz,hpin,hscore,hdev⟩ := full_supported_selection
    (by simp : 2≤Fintype.card A) Prod.fst COL
    (fun r => by
      convert hrow r using 1
      congr 1
      exact Finset.ext fun w => by simp only [Finset.mem_filter])
    (fun p => by
      convert clone_degree ends cycle p using 1
      congr 1
      exact Finset.ext fun w => by simp only [Finset.mem_filter])
    (fun c => by
      convert ordinary_degree ends cycle c using 1
      congr 1
      exact Finset.ext fun w => by simp only [Finset.mem_filter])
    reference ref
  let label := wordLabel Prod.fst COL z
  let b := ceilCopies (2^(T+1)) (realMaximum label)
  refine ⟨z,?_,?_,?_,?_⟩
  · have h8 : 8≤L := (by decide : 8≤131072).trans hL
    have h16 : 16≤Δ := (Nat.mul_le_mul_left 2 h8).trans p3
    exact collision_of_joint (by simp) Prod.fst COL z ref Δ h16
      (show JointScore Prod.fst COL z ≤ 32*(M:ℚ) from hscore)
  · have he' : allCenter A Pair (OrdinaryWire Pair H) T = mu N C := by
      unfold allCenter mu
      rw [hM,printed_denom A hA,Nat.cast_mul,Nat.cast_ofNat]
    have hv : 32*(M:ℚ) ≤ (rho N C)^2 := by simpa only [hM,Nat.cast_mul,Nat.cast_ofNat] using hmargin.word
    have hc : allCenter A Pair (OrdinaryWire Pair H) T + rho N C ≤
        (bUpper N C L : ℚ)*2^(T+1) := by
      rw [he']; simpa only [printedL,Nat.cast_pow,Nat.cast_ofNat] using hmargin.capacity
    have hcap := capacity_of_deviation Prod.fst COL z (rho N C) hmargin.rho_nonneg hc
      (fun d => (hdev d).1.trans hv)
    have hb : b ≤ bUpper N C L := ceilCopies_le (by positivity) (real_maximum_le _ _ hcap)
    have hbp : (b:ℚ)*L ≤ 3*mu N C :=
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hb) (by positivity)).trans hmargin.padded
    have hp : Nat.card (Page (T+1) b A)*L = C*(b*L) := by
      have hh := total_slots (J7SeatPacking.balancedMask (K:=A) (T+1) b)
      rw [total_cells,hA] at hh
      exact hh
    change Nat.card (Page (T+1) b A)*L ≤ 3*Nat.card W
    rw [hp,Nat.card_eq_fintype_card,hM]
    have hD : (0:ℚ)<C := by exact_mod_cast printedD_pos T
    have ht := mul_le_mul_of_nonneg_left hbp hD.le
    unfold mu at ht
    have h' : (C:ℚ)*((b:ℚ)*L) ≤ 3*(24*(N:ℚ)) := by
      have he : (C:ℚ)*(3*(24*(N:ℚ)/C)) = 3*(24*(N:ℚ)) := by
        rw [mul_left_comm, mul_div_cancel₀ _ hD.ne']
      exact he ▸ ht
    exact_mod_cast h'
  · intro pin
    simpa [label,wordLabel] using hpin pin
  · have hcent : allCenter A Pair (OrdinaryWire Pair H) T = mu N C := by
      unfold allCenter mu
      rw [hM,printed_denom A hA,Nat.cast_mul,Nat.cast_ofNat]
    have hpcent : pinCap A Pair T = pinMeanUpper N C := by
      unfold pinCap pinMeanUpper
      rw [hA,printed_denom A hA]
      norm_num
    have hv : 32*(M:ℚ) ≤ (rho N C)^2 := by simpa only [hM,Nat.cast_mul,Nat.cast_ofNat] using hmargin.word
    have hc : allCenter A Pair (OrdinaryWire Pair H) T + rho N C ≤
        (bUpper N C L : ℚ)*2^(T+1) := by
      rw [hcent]; simpa only [printedL,Nat.cast_pow,Nat.cast_ofNat] using hmargin.capacity
    have hcap := capacity_of_deviation Prod.fst COL z (rho N C) hmargin.rho_nonneg hc
      (fun d => (hdev d).1.trans hv)
    have hb : b ≤ bUpper N C L := ceilCopies_le (by positivity) (real_maximum_le _ _ hcap)
    have cap (c : CELL) : Nat.card (RealFiber label c) ≤ b*2^(T+1) :=
      padded_real_cap label _ (real_maximum_point label) c
    let quota := 4*b+(⌈delta N C⌉ : ℤ).toNat
    have qmargin (c : CELL) : (quota:ℚ) + delta N C ≤
        (Nat.card {w : {w : W // nonpin COL w} // label w.val = c} : ℚ)*(1/2:ℚ)^5 := by
      let d := (cellChartEq A T).symm c
      have ht := (hdev d).1.trans hv
      have hp₀ := (hdev d).2.trans hv
      have hp : ((∑ e ∈ pinWires Pair (OrdinaryWire Pair H), indicator (fullCell Prod.fst COL e z) d) -
          (if d.1.1=d.2.1 then 0 else pinCap A Pair T))^2 ≤ (rho N C)^2 := by
        by_cases same : d.1.1=d.2.1
        · simpa only [if_pos same] using hp₀
        · simpa only [if_neg same] using hp₀
      have hl := deviation_lower _ _ _ hmargin.rho_nonneg ht
      have hu := deviation_lower
        (-(∑ w ∈ pinWires Pair (OrdinaryWire Pair H), indicator (fullCell Prod.fst COL w z) d))
        (-(if d.1.1 = d.2.1 then 0 else pinCap A Pair T)) _
        hmargin.rho_nonneg (by rw [show ∀ x y : ℚ, (-x - -y)^2 = (x-y)^2 by intros; ring]; exact hp)
      have hpc : 0≤pinCap A Pair T := by rw [hpcent]; unfold pinMeanUpper; positivity
      have hu' : (∑ w ∈ pinWires Pair (OrdinaryWire Pair H), indicator (fullCell Prod.fst COL w z) d) ≤
          pinCap A Pair T + rho N C := by
        by_cases same : d.1.1=d.2.1
        · rw [if_pos same] at hu; linarith
        · rw [if_neg same] at hu; linarith
      have he := nonpin_count_as_difference Prod.fst COL z d
      rw [Equiv.apply_symm_apply] at he
      change allCenter A Pair (OrdinaryWire Pair H) T - rho N C ≤ _ at hl
      change (quota:ℚ) + delta N C ≤ _ * (1/2:ℚ)^5
      have h0 : (quota:ℚ) ≤ 4*(bUpper N C L:ℚ)+(⌈delta N C⌉ : ℤ).toNat := by
        unfold quota
        push_cast
        have hb' : (b:ℚ) ≤ bUpper N C L := by exact_mod_cast hb
        linarith
      apply (add_le_add_right h0 _).trans
      apply (enlargedMatchingMargin (printedD_pos T) hL p2).trans
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [he]
      rw [← hcent,← hpcent]
      linarith
    have hnum : (Nat.card {w : W // nonpin COL w}:ℚ) ≤ 24*(N:ℚ) := by
      have hn := Fintype.card_subtype_le (fun w : W => nonpin COL w)
      rw [hM] at hn
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast hn
    obtain ⟨matched,hm,hr,_,hcount⟩ := matching_from_cell_quota (nonpin COL)
      (rowNode Prod.fst) (colNode COL) label quota (delta N C) hmargin.delta_nonneg
      ((mul_le_mul_of_nonneg_right hnum (by positivity)).trans hmargin.mark)
      (physical_degree_le_five Prod.fst COL ordinary_row_exact_two
        (fun p => by
          convert clone_degree ends cycle p using 1
          congr 1
          exact Finset.ext fun w => by simp only [Finset.mem_filter])
        (fun c => by
          convert ordinary_degree ends cycle c using 1
          congr 1
          exact Finset.ext fun w => by simp only [Finset.mem_filter])) qmargin
    have hE : Fintype.card E ≤ 24*N := by
      simp only [Clones, Index, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
      let n := Fintype.card Pair * 2
      change n*4 ≤ 24*n
      simpa only [Nat.mul_comm n 4] using Nat.mul_le_mul_right n (by decide : 4≤24)
    have sq : Real.sqrt B ≤ ((delta N C : ℚ):ℝ) := by
      rw [hM]
      push_cast
      simpa only [printedL,Nat.cast_pow,Nat.cast_ofNat] using
        (@sqrtMarkBudget_le_delta N C L Δ (Fintype.card E) ((by decide : 2≤131072).trans hL) hE hmargin)
    have qbound : (3*(b:ℝ)) + ((delta N C : ℚ):ℝ) ≤ quota := by
      have hc := (upper_rounding (delta N C) hmargin.delta_nonneg).1
      have hc' : ((delta N C : ℚ):ℝ) ≤ (⌈delta N C⌉ : ℤ).toNat := by exact_mod_cast hc
      unfold quota
      push_cast
      linarith [show 0≤(b:ℝ) by positivity]
    have hsub (c : CELL) : (ofCell label matched c).card ≤ Nat.card (RealFiber label c) := by
      let emb : {w // w∈ofCell label matched c} ↪ RealFiber label c :=
        ⟨fun w => ⟨w.val,(Finset.mem_filter.mp w.prop).2⟩,
          fun _ _ h => Subtype.ext (congrArg (fun x : RealFiber label c => x.val) h)⟩
      simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using Nat.card_le_card_of_injective emb emb.injective
    have hmarg (c : CELL) : 2*(b:ℝ)+(ofCell label matched c).card/(2^(T+1):ℕ)+Real.sqrt B ≤
        (ofCell label matched c).card := by
      have ht : ((ofCell label matched c).card:ℝ)/(2^(T+1):ℕ) ≤ b := by
        apply (div_le_iff₀ (by positivity)).2
        exact_mod_cast (hsub c).trans (cap c)
      have hk : (quota:ℝ) ≤ (ofCell label matched c).card := by exact_mod_cast hcount c
      linarith
    have hmp : matched ⊆ publicNonpins ends := by
      intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp (hm hw)).2⟩
    have hn (c : CELL) : 2*b ≤ (ofCell label (publicNonpins ends) c).card := by
      apply le_trans _ ((hcount c).trans (Finset.card_le_card (Finset.filter_subset_filter _ hmp)))
      exact (Nat.mul_le_mul_right b (by decide : 2≤4)).trans (Nat.le_add_right _ _)
    obtain ⟨seat,keep,hd,hq,hl,hs,_,hnp,hR⟩ := literalJointPlacement ends (a:=T+1) (b:=b) label
      (Nat.zero_lt_succ T) matched hmp hr cap hn hmarg
    exact ⟨seat,keep,hd,hq,hl,hs,hnp,hR⟩

#print axioms literalJointPrintedSeats
end
end Paper6JointSeating




