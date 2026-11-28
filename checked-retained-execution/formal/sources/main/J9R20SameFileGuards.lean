
import J9R20SameFileCatalog
import J6R16SpecializedBoxRoot
import J7R13Schedule
import J9R18CompiledSmallScope

/-! Remove the duplicate Ready/Stable assumptions for the original
large four-clone input. These are properties of the same untouched file
and real printed source size; the standard RootBounds certificate for
the extension and induction remains explicit. -/
namespace J9R20SameFile
open scoped Polynomial Classical BigOperators
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R12Blueprint
open J6R14SpecializedBox J6R11Blueprint J6ActiveRun J1PPrinted
open J8EndToEnd J8Physical J7PrintedParams J7PrintedParamsGraph J7ToJ8Incidence J7SourceLabels
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000

private theorem nat_le_pow_two (n : ℕ) : n≤2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : 0<2^n := by positivity
    rw [pow_succ]
    omega

theorem four_clone_ready_and_printed_guards
    {Pair H Packet R : Type} [Fintype Pair] [Fintype H] [Fintype Packet] [Fintype R]
    {L : ℕ} (ends : H×Bool≃Pin Pair×Fin 3)
    (d : Layout Packet R (Pin Pair) (PrintedOld Pair H) (Fin 64) (Ports (column ends cycle)) L)
    (F : OldTables d) (sign : Pin Pair→Bool)
    (f : ℤ[X]) (ell created : ℕ)
    (large : 2^(9*131072-1) < sourceSize (Fintype.card (Pin Pair)))
    (cfg : RootBounds (sourceSize (Fintype.card (Pin Pair))) 3 f) :
    let s := sourceSize (Fintype.card (Pin Pair))
    let A := stepA (Nat.clog 2 s) 0
    let M := Fintype.card (J8Physical.Wire R)
    let r := orientedRootCall d f ell created F sign
    Stable s 3 r ∧ Ready (printedParams s) (sourceDelta s) r ∧
      (0<A) ∧ (0<stepU (Nat.clog 2 s) 0) ∧ (stepU (Nat.clog 2 s) 0≤M) ∧
      Even (2^A:ℕ) ∧ (36≤(2^A:ℕ)) ∧ (2^A:ℕ)^3≤M := by
  dsimp only
  let n := Fintype.card (Pin Pair)
  let s := sourceSize n
  let a := stepA (Nat.clog 2 s) 0
  let t := rootT s
  let M := Fintype.card (J8Physical.Wire R)
  have he : n%2=0 := (actual_incidence ends).2
  have hw : M=24*n := (Fintype.card_congr (d.column.trans (colWire (column ends cycle)))).trans
    (actual_incidence ends).1
  have hU : 9≤rootU s := u_large s large
  have hs : 2*s=21*n := (source_size n he).1
  have cap := four_clone_root_packing n he large
  have hu0 : 0<rootU s := lt_of_lt_of_le (by decide : (0:ℕ)<9) hU
  have hlog : 0<Nat.clog 2 s := by
    have h := (Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).2 large
    exact lt_trans (by decide : (0:ℕ)<9*131072-1) h
  have hdelta : 2*printedL t≤sourceDelta s := by
    rw [← J7R13.root_delta_same]
    exact cap.2.2.2
  have hlower : 131072≤printedL t := cap.1
  have hd : 3≤sourceDelta s := Nat.le_trans
    ((by decide : (3:ℕ) ≤ 2*131072)) (Nat.le_trans (Nat.mul_le_mul_left _ hlower) hdelta)
  have hcap : M≤3*s := by clear large; omega
  have stable : Stable s 3 (orientedRootCall d f ell created F sign) :=
    literal_oriented_root_stable d f ell created F sign hcap ((by decide : (2:ℕ)≤3).trans hd)
      (fun v => (J9R18Compiled.fourClone_port_count ends v).trans hd)
  have hactive : (printedParams (f:=f) (ell:=ell) s).cutoff <
      (orientedRootCall d f ell created F sign).edges := by
    change J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) < M
    rw [← J7R13.root_cutoff_same s hlog,hw]
    exact four_clone_root_active n he large
  have ready := getReady cfg stable hactive
  have ha : a=t+1 := J7R13.root_bits_same s hu0
  have hU' : stepU (Nat.clog 2 s) 0 = rootU s := J7R13.root_width_same s
  have aPos : 0<a := by rw [ha]; exact Nat.zero_lt_succ t
  have uPos : 0<stepU (Nat.clog 2 s) 0 := by rwa [hU']
  have hlm : (2^a:ℕ) ≤ M := by
    rw [hw,ha]
    exact (Nat.le_mul_of_pos_right _ (printedD_pos t)).trans cap.2.2.1
  have even : Even (2^a:ℕ) := by
    rw [ha,pow_succ]
    exact ⟨2^t,by omega⟩
  have hbig : (36:ℕ) ≤ 2^a := by
    rw [ha]; exact (by decide : (36:ℕ) ≤ 131072).trans cap.1
  have cubic : (2^a:ℕ)^3≤M := by
    have hh := cap.2.2.1
    rw [printedD_is_L12,← pow_succ'] at hh
    rw [ha,hw]
    change (printedL t)^3≤_
    exact (Nat.pow_le_pow_right (by unfold printedL; positivity) (by decide : 3≤13)).trans hh
  have huM : stepU (Nat.clog 2 s) 0≤M := by
    have hFit := ready.widthFits
    change stepU (Nat.clog 2 s) 0 ≤ a at hFit
    exact hFit.trans ((nat_le_pow_two a).trans hlm)
  exact ⟨stable,ready,aPos,uPos,huM,even,hbig,cubic⟩

/-- Once L≥36 the lower window contains an integral linear precision,
2 bits per original pin = M/12 bits. The sharper rational threshold
is the head of the main theorem. -/
theorem linear_low_budget (L n : ℕ) (hL : 36≤L) :
    (2*n:ℚ)≤(24*(n:ℚ))/6-3*(24*(n:ℚ))/(L:ℕ) := by
  have hLq : (0:ℚ)<(L:ℚ) := by exact_mod_cast (show 0<L by omega)
  have hdegree : (36:ℚ) ≤ (L:ℚ) := by exact_mod_cast hL
  have hp : 3*(24*(n:ℚ))/(L:ℕ)≤2*(n:ℚ) := by
    apply (div_le_iff₀ hLq).mpr
    nlinarith only [hdegree,show (0:ℚ)≤(n:ℚ) by positivity, mul_nonneg
      (sub_nonneg.mpr hdegree) (show (0:ℚ)≤(n:ℚ) by positivity)]
  linarith

#print axioms four_clone_ready_and_printed_guards
#print axioms linear_low_budget
end
end J9R20SameFile
