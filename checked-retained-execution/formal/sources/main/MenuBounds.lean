import SourceBarrier
import LogarithmicBudget
import Mathlib.Data.Fintype.Powerset

/-!
# Counting distinct coordinate cuts

Each menu entry is determined by its coordinate and its subset of the
alphabet. The resulting count and second-moment scale are derived from the
actual menu. A source-certificate theorem uses these counts with the
published logarithmic coordinate schedule.
-/

namespace MenuBounds

open scoped BigOperators

section Counts

variable {I A J : Type*} [Fintype I] [Fintype A] [Fintype J]

/-- An alphabet with r symbols has precisely 2^r symbol subsets. -/
theorem menu_card_le (owner : J → I) (symbols : J → Finset A)
    (hinj : Function.Injective (fun j => (owner j, symbols j))) :
    Fintype.card J ≤ Fintype.card I * 2 ^ Fintype.card A := by
  simpa only [Fintype.card_prod, Fintype.card_finset] using Fintype.card_le_of_injective _ hinj

omit [Fintype I] in
/-- When the coordinate is fixed, its symbol subset still determines the
menu entry. -/
theorem coordinate_count_le [DecidableEq I] (owner : J → I) (symbols : J → Finset A)
    (hinj : Function.Injective (fun j => (owner j, symbols j))) (i : I) :
    ProductVariance.coordinateCount owner i ≤ 2 ^ Fintype.card A := by
  let fiber := Finset.univ.filter (fun j => owner j = i)
  let code (j : fiber) := symbols j
  have hcode : Function.Injective code := by
    intro j k hs
    apply Subtype.ext (hinj ?_)
    apply Prod.ext _ hs
    exact (Finset.mem_filter.mp j.property).2.trans (Finset.mem_filter.mp k.property).2.symm
  simpa only [Fintype.card_coe, Fintype.card_finset, fiber, ProductVariance.coordinateCount] using
    Fintype.card_le_of_injective code hcode

theorem sum_coordinate_squares_le [DecidableEq I] (owner : J → I) (symbols : J → Finset A)
    (hinj : Function.Injective (fun j => (owner j, symbols j))) :
    (∑ i, (ProductVariance.coordinateCount owner i) ^ 2) ≤
      Fintype.card I * 2 ^ (2 * Fintype.card A) := by
  calc
    _ ≤ ∑ _i : I, (2 ^ Fintype.card A) ^ 2 := Finset.sum_le_sum fun i _ =>
      Nat.pow_le_pow_left (coordinate_count_le owner symbols hinj i) _
    _ = _ := by simp [← pow_mul, Nat.mul_comm (Fintype.card A) 2]

/-- The source density constant is twenty. -/
def countedScale (k r : ℕ) : ℕ :=
  FiniteGrowth.integerScale (20 * k * 2 ^ (2 * r))

def squaredScaleCap (r : ℕ) : ℕ := 80 * 2 ^ (2 * r)

theorem countedScale_pos (k r : ℕ) : 1 ≤ countedScale k r := by
  unfold countedScale FiniteGrowth.integerScale
  omega

theorem countedScale_dominates [DecidableEq I] (owner : J → I) (symbols : J → Finset A)
    (hinj : Function.Injective (fun j => (owner j, symbols j))) :
    20 * (∑ i, (ProductVariance.coordinateCount owner i : ℚ) ^ 2) ≤
      (countedScale (Fintype.card I) (Fintype.card A) : ℚ) ^ 2 := by
  have h : 20 * (∑ i, (ProductVariance.coordinateCount owner i) ^ 2) ≤
      countedScale (Fintype.card I) (Fintype.card A) ^ 2 := calc
    _ ≤ 20 * (Fintype.card I * 2 ^ (2 * Fintype.card A)) := Nat.mul_le_mul_left _
      (sum_coordinate_squares_le owner symbols hinj)
    _ = 20 * Fintype.card I * 2 ^ (2 * Fintype.card A) := by ring
    _ ≤ _ := (Nat.lt_succ_sqrt' _).le
  exact_mod_cast h

theorem countedScale_upper (k r : ℕ) (hk : 0 < k) :
    countedScale k r ^ 2 ≤ squaredScaleCap r * k := by
  have hs : 0 < 20 * k * 2 ^ (2 * r) := by positivity
  calc
    _ ≤ 4 * (20 * k * 2 ^ (2 * r)) := (FiniteGrowth.integerScale_bounds _ hs).2.2
    _ = _ := by unfold squaredScaleCap; ring

end Counts

variable {V P I A J T R S K : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V] [Fintype P]
variable [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype J] [Nonempty J] [Fintype T]
variable [CommRing R] [CommRing S] [Nontrivial S] [Field K]

/-- An actual distinct menu of balanced symbol subsets, a certified port
layout, and a cubic expanding graph give a logarithmic-budget lower bound.
The proof chooses H, counts the cuts, and verifies the selection budget. -/
theorem source_distinct_menu_barrier (E : Finset (V × V)) (pin : V ↪ P)
    (cell : P → (I → A) × (I → A)) (kept : Finset I) (owner : J → kept) (symbols : J → Finset A)
    (hinj : Function.Injective (fun j => (owner j, symbols j)))
    (Δ γ η : ℚ) (hcert : SourceDensity.CollisionCertificate cell Δ)
    (hports : Fintype.card P = 10 * Fintype.card V) (hloop : ∀ v, (v, v) ∉ E)
    (hregular : ∀ v, GraphCutMoments.degree E v = 3)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1 / 2)
    (hexp : ∀ U : Finset V,
      γ * (min U.card (Fintype.card V - U.card) : ℕ) ≤ ((GraphCutMoments.boundary E U).card : ℚ))
    (hbalance : ∀ j, η * Fintype.card V ≤
      (min (EmpiricalCutMoments.labelCut (SourceBarrier.labels pin cell kept) owner symbols j).card
        (Fintype.card V -
          (EmpiricalCutMoments.labelCut (SourceBarrier.labels pin cell kept) owner symbols j).card) : ℕ))
    (hcoords : kept.card ≤ 2 * LogarithmicBudget.activeCoordinates (7 * Fintype.card V / 2))
    (hN : LogarithmicBudget.cutoff (LogarithmicBudget.multiplier (2 ^ Fintype.card A : ℕ)
      (squaredScaleCap (Fintype.card A)) (FiniteGrowth.coefficient γ η)) 3 ≤ Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R) (terms : T → SeparatedRank.VertexTerm V K) (assigned : T → J)
    (hside : ∀ z, (terms z).side =
      EmpiricalCutMoments.labelCut (SourceBarrier.labels pin cell kept) owner symbols (assigned z))
    (hrepresentation : ∀ σ, embed (output σ) = ∑ z, (terms z).value σ)
    (hcorrect : ∀ σ, residue (output σ) = (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S)) :
    ∃ d : ℕ, (FiniteGrowth.coefficient γ η * Fintype.card V) ^ 2 ≤
      4 * (squaredScaleCap (Fintype.card A) : ℚ) * (((Fintype.card V).log2 + 3 : ℕ) : ℚ) * (d : ℚ) ^ 2 ∧
      2 ^ d ≤ Fintype.card T := by
  let k := Fintype.card kept
  let r := Fintype.card A
  have hk : 0 < k := Fintype.card_pos_iff.mpr ⟨owner (Classical.choice inferInstance)⟩
  let G : SourceBarrier.Geometry E pin cell kept owner symbols := {
    delta := Δ, certificate := hcert, ports := hports, loopless := hloop, regular := hregular
    gamma := γ, eta := η, H := countedScale k r
    gamma_pos := hγ, gamma_le_one := hγ1, eta_pos := hη, eta_le_half := hη1
    H_ge_one := by exact_mod_cast countedScale_pos k r
    expansion := hexp, balance := hbalance, scale := countedScale_dominates owner symbols hinj }
  have hmenu : (Fintype.card J : ℚ) ≤ ((2 ^ r : ℕ) : ℚ) * k := by
    exact_mod_cast (menu_card_le owner symbols hinj).trans_eq (Nat.mul_comm _ _)
  have hscale : G.toLabelGeometry.H ^ 2 ≤ (squaredScaleCap r : ℚ) * k := by
    change (countedScale k r : ℚ) ^ 2 ≤ _
    exact_mod_cast countedScale_upper k r hk
  have hu : k ≤ (Fintype.card V).log2 + 3 := by
    simpa only [k, Fintype.card_coe] using hcoords.trans
      (LogarithmicBudget.source_root_coordinates_le_log (Fintype.card V))
  exact LogarithmicBudget.logarithmic_modular_barrier G.toLabelGeometry k 3 (2 ^ r : ℕ)
    (squaredScaleCap r) (Nat.cast_nonneg _) hmenu hscale hu hN embed residue hinjective
    output terms assigned hside hrepresentation hcorrect

#print axioms menu_card_le
#print axioms coordinate_count_le
#print axioms sum_coordinate_squares_le
#print axioms countedScale_pos
#print axioms countedScale_dominates
#print axioms countedScale_upper
#print axioms source_distinct_menu_barrier

end MenuBounds
