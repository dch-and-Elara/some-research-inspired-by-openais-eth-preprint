import J7R10Plant
import J6PhysicalInteger

/-!
# Anchored raw-CNF count through the printed J6 receiver

This composes the now-concrete old plant with the actual finite
physical register, signed integer receiver and ordinary interpolation.
The public mask, layout word and root half-length are supplied.
This is direct register acquisition, not a proof of the active
recursive nonzero-probe evaluator or of query acquisition time.
-/

open Std.Sat
open scoped BigOperators Polynomial Classical

namespace J7R10Readout
open P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval J6RepairedCentered
open J6NativeHeightMesh J6ZeroTransport J6IntegerLayers J6IntegerDecode
open J7R10Plant
set_option maxHeartbeats 1750000

variable {S W : Type*} [LinearOrder S] [Fintype S] [Fintype W]

noncomputable def actualNumerator
    (m q base l : ℕ) (host : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (h : m≤K m) (hl : 2*l=L m) (i : J6Recovery.Addr m) : ℤ :=
  letI : DecidableEq (Pad w m (K m) l) := Classical.decEq _
  let p := J6SourcePrecision.printed m base
  let n := sampleNum m i
  let d := sampleDen m i
  let z := J6NativeHeightResidue.residueSlot (oldOK host w) (newOK host w)
    (fun k x => ((shiftAt m l mask w h hl i k).map x).getD false)
    (reduceBase p (J6NativeHeightDyadic.scalar m i))
  (integerDecode p (J6Recovery.exp m i) (M m) d
    (factor (P:=Fin m) n d (index m i) q
      (J6PhysicalInteger.loads m l mask w h hl i)) z).1

theorem numeral_exact (m q base l : ℕ) (host : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (h : m≤K m) (hl : 2*l=L m) (hS : Fintype.card S=64)
    (hz : coreA host (fun _ => false)=true) (i : J6Recovery.Addr m) :
    actualNumerator m q base l host mask w h hl i =
      oldLayer (coreA host) (coreB host) (sampleNum m i) (sampleDen m i) := by
  exact congrArg Prod.fst
    (J6PhysicalInteger.printed_receiver_no_fit_assumption m base l q mask w h hl host hz i hS)

noncomputable def layer (m q : ℕ) (host : Plant W m q) : ℚ[X] :=
  LayerRecovery.layerPolynomial (J6OrientedPlantValue.wt (coreA host))
    (J6OrientedPlantValue.wt (coreB host))

noncomputable def sample
    (m q base l : ℕ) (host : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (h : m≤K m) (hl : 2*l=L m) (i : J6Recovery.Addr m) : ℚ :=
  (actualNumerator m q base l host mask w h hl i:ℚ)/(sampleDen m i:ℚ)^m

theorem sample_exact (m q base l : ℕ) (host : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (h : m≤K m) (hl : 2*l=L m) (hS : Fintype.card S=64)
    (hz : coreA host (fun _ => false)=true) (i : J6Recovery.Addr m) :
    sample m q base l host mask w h hl i=(layer m q host).eval (point m i) := by
  have hd := (mesh_bounds m i).1.ne'
  have hpow : (sampleDen m i:ℚ)^m≠0 := pow_ne_zero _ (by exact_mod_cast hd)
  unfold sample
  rw [numeral_exact m q base l host mask w h hl hS hz,
    oldLayer_cast _ _ _ _ hd,Fintype.card_fin,← mesh_fraction,
    mul_div_cancel_left₀ _ hpow]
  rfl

noncomputable def reconstructed
    (m q base l : ℕ) (host : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (h : m≤K m) (hl : 2*l=L m) : ℚ[X] :=
  Lagrange.interpolate Finset.univ (point m) (sample m q base l host mask w h hl)

theorem reconstructed_exact (m q base l : ℕ) (host : Plant W m q)
    (mask : MaskFamily (a m) (K m) S) (w : Fin (a m) → S)
    (h : m≤K m) (hl : 2*l=L m) (hS : Fintype.card S=64)
    (hz : coreA host (fun _ => false)=true) :
    reconstructed m q base l host mask w h hl=layer m q host := by
  have hn : (layer m q host).natDegree < (Finset.univ : Finset (J6Recovery.Addr m)).card := by
    have hdeg := LayerRecovery.layerPolynomial_degree
      (J6OrientedPlantValue.wt (coreA host)) (J6OrientedPlantValue.wt (coreB host))
    simp only [Fintype.card_fin] at hdeg
    change (layer m q host).natDegree ≤ m at hdeg
    simp [Finset.card_univ]
    omega
  have hdegree : (layer m q host).degree < ↑(Finset.univ : Finset (J6Recovery.Addr m)).card :=
    Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hn)
  symm
  exact Lagrange.eq_interpolate_of_eval_eq (sample m q base l host mask w h hl)
    (negative_distinct_points m).2.injOn hdegree (fun i _ =>
      (sample_exact m q base l host mask w h hl hS hz i).symm)

variable {V : Type*} [DecidableEq V] [Fintype V] [Nonempty V]

noncomputable abbrev H (F : CNF V) := J7R9SourceInput.H F
noncomputable abbrev mCNF (F : CNF V) := nWires (H F)
noncomputable abbrev qCNF (F : CNF V) := nSubdiv (H F)

theorem raw_count_at_origin
    (F : CNF V) (base l : ℕ)
    (mask : MaskFamily (a (mCNF F)) (K (mCNF F)) S)
    (w : Fin (a (mCNF F)) → S)
    (h : mCNF F ≤ K (mCNF F)) (hl : 2*l=L (mCNF F)) (hS : Fintype.card S=64) :
    (reconstructed (mCNF F) (qCNF F) base l (physicalPlant (H F)) mask w h hl).eval 1 - 1 =
      (PinnedCNF.modelCount F:ℚ) := by
  rw [reconstructed_exact _ _ _ _ _ _ _ _ _ hS (planted_guard_zero F)]
  change (LayerRecovery.layerPolynomial _ _).eval 1 - 1 = _
  rw [guarded_origin_exact F]
  push_cast
  ring

def meshHalf (m : ℕ) : ℕ := L m / 2

theorem meshHalf_exact (m : ℕ) : 2*meshHalf m=L m := by
  obtain ⟨k,hk⟩ := (mesh_seats m).2.2
  unfold meshHalf
  omega

theorem printed_raw_count_from_mask
    (F : CNF V) (base : ℕ)
    (mask : MaskFamily (a (mCNF F)) (K (mCNF F)) S)
    (w : Fin (a (mCNF F)) → S) (hS : Fintype.card S=64) :
    let m := mCNF F
    let q := qCNF F
    let l := meshHalf m
    let h : m≤K m := by have := (mesh_seats m).2.1; omega
    (reconstructed m q base l (physicalPlant (H F)) mask w h (meshHalf_exact m)).eval 1 - 1 =
      (PinnedCNF.modelCount F:ℚ) := by
  dsimp only
  exact raw_count_at_origin F base _ mask w _ (meshHalf_exact _) hS

#print axioms numeral_exact
#print axioms sample_exact
#print axioms reconstructed_exact
#print axioms raw_count_at_origin
#print axioms printed_raw_count_from_mask

end J7R10Readout

