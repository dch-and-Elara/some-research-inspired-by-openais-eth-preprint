
import J6R26StablePreparedRootSite
import J6R25StableCensusCard
import J7R10Plant
import J6R24LegalLayoutBudget

/-! Recover the printed root guards from the literal guarded 3CNF
parameters. The sufficiently-large threshold is not pretended automatic. -/
namespace J6R28GeneratedRootFrame
open scoped Polynomial
open Polynomial Std.Sat J6Mesh J6OrientedHost J7R10Plant
open J6R24LegalLayout J6R26StablePreparedRoot J6R12Repack J6R11Repack
open J1PPrinted J6ActiveRun J6R11Threshold
set_option maxHeartbeats 6000000
set_option maxRecDepth 1600
set_option linter.unusedSectionVars false

noncomputable def literalNativeSize {V : Type} [DecidableEq V] [Fintype V] (F : CNF V) : ℕ :=
  Fintype.card (Option V)+(J7R9SourceInput.H F).length

theorem literal_native_fits {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (F : CNF V) (h : ∀ c∈F,c.length≤3) :
    literalNativeSize F≤J7R10Readout.mCNF F :=
  (J7R9SourceInput.source_count_size F h).2.2.1

theorem root_delta_at_least_four {V : Type} [Fintype V]
    (f : ℤ[X]) (m q b native : ℕ) (T : Plant V m q) (w : Fin (a m)→Fin 64)
    (hn : native≤m)
    (large : (2*epsDen)^30*(2:ℕ)^10 ≤ Nat.clog 2 (physicalSize m native)) :
    4≤sourceDelta (physicalSize m native) := by
  let s := physicalSize m native
  obtain ⟨_,_,hu⟩ := printed_size_implies_numeric_guards s 2 (by decide) large
  have hact := (actual_printed_root_ready_size f 1 b m (printedHalf m) q native T w
    (fun _ _ _=>false) (printed_room m) (printed_half_correct m) (Fintype.card_fin 64)
    hn (0:Fin 64)).2.2.1
  have ht : J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)<M m := hact
  have hm := (source_packing_conditions s (M m) 0 hu ht).2.2
  have h2 : 2≤stepL (Nat.clog 2 s) 0 := by
    unfold stepL
    rw [mesh_root_bits m native hn]
    calc
      2 = (2:ℕ)^1 := by decide
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (J6R24LegalLayout.odd_axis_available m)
  exact (Nat.mul_le_mul_left 2 h2).trans hm

noncomputable def guarded_printed_root_shape
    {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
    (F : CNF V) (h : ∀ c∈F,c.length≤3) (f : ℤ[X]) (base : ℕ)
    (w : Fin (a (J7R10Readout.mCNF F))→Fin 64)
    (field : f.natDegree=4*Nat.clog 2 (physicalSize (J7R10Readout.mCNF F) (literalNativeSize F)))
    (large : (2*epsDen)^30*(2:ℕ)^10 ≤
      Nat.clog 2 (physicalSize (J7R10Readout.mCNF F) (literalNativeSize F))) :
    RootShape f (J7R10Readout.mCNF F) (printedHalf (J7R10Readout.mCNF F))
      base (literalNativeSize F) (printedRankWidth (J7R10Readout.mCNF F))
      (physicalPlant (J7R10Readout.H F)) w := by
  let m := J7R10Readout.mCNF F
  let q := J7R10Readout.qCNF F
  let native := literalNativeSize F
  let T := physicalPlant (J7R10Readout.H F)
  have hn : native≤m := literal_native_fits F h
  have h4 := root_delta_at_least_four f m q base native T w hn large
  exact ⟨printed_room m,printed_half_correct m,hn,(printed_rank_width m).2.1,
    (printed_rank_width m).2.2,field,large,fun v=>(planted_guard_degree F h v).trans h4⟩

#print axioms literal_native_fits
#print axioms root_delta_at_least_four
#print axioms guarded_printed_root_shape
end J6R28GeneratedRootFrame
