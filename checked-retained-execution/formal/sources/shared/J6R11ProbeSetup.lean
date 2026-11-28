import J6R10ReachablePrinted
import J6R10ProbeFieldZero

namespace J6R11ProbeSetup
open scoped Classical Polynomial
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J1PPrinted
open NativeProbeRing

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
variable {Values : ℕ → Type*} {s : ℕ} {W : Call Host → ℤ → Mode → ℕ}

/-- One monic lift and one word enumeration serve every active call and
every probe precision. The substantive timetable inputs are the printed
source thresholds, not a constraint on arbitrary fabricated call records. -/
theorem shared_field_and_words (s : ℕ) (hs : 0 < Nat.clog 2 s) :
    ∃ f : ℤ[X], f.Monic ∧ f.natDegree = 4 * Nat.clog 2 s ∧ Irreducible (residuePoly f) ∧
      ∃ words : Fin (2^(4*Nat.clog 2 s)) → Fin f.natDegree → Bool,
        words ⟨0,pow_pos (by decide) _⟩ = (fun _ => false) ∧
        ∀ p, 0 < p →
          probe p f (words ⟨0,pow_pos (by decide) _⟩)=0 ∧
          ∀ i j, i≠j → IsUnit (probe p f (words j)-probe p f (words i)) := by
  exact J6R10ProbeFieldZero.zero_in_uniform_menu
    (4 * Nat.clog 2 s) (2 ^ (4 * Nat.clog 2 s)) (by omega) (by positivity) le_rfl

/-- Quantitative preconditions discharged for every genuinely reachable
active call, using the same probe-ring polynomial fixed at the root. -/
theorem active_call_feasible (P : Program (printedShape s W) Values) (root c : Call Host)
    (h : Reach P root c) (rootDepth : root.depth = 0)
    (C : ℕ) (hC : 0 < C) (hCs : C ≤ s) (seed : root.edges ≤ C*s)
    (hU : 1 ≤ J9PrintedSchedule.rootU (Nat.clog 2 s))
    (hsize : (2*epsDen)^30*C^10 ≤ Nat.clog 2 s)
    (hactive : (printedShape s W).cutoff < c.edges)
    (f : ℤ[X]) (hf : f.natDegree = 4*Nat.clog 2 s) :
    ProofFit (printedShape s W) f c ∧
      (1 ≤ (printedShape s W).levelWidth c.depth ∧
       (printedShape s W).levelWidth c.depth ≤ (printedShape s W).levelBits c.depth ∧
       (printedShape s W).levelWidth c.depth ≤ c.edges) ∧
      let L := 2^(printedShape s W).levelBits c.depth
      let D := stepD (Nat.clog 2 s) c.depth
      2*D^2*sourceDelta s ≤ c.edges ∧ L*D ≤ c.edges ∧ 2*L ≤ sourceDelta s := by
  refine ⟨printed_probe_fit_reachable h rootDepth C seed hCs hU hactive f hf,
    printed_taper_reachable h rootDepth C seed hC hU hsize hactive, ?_⟩
  exact printed_pack_reachable hU hactive

#print axioms shared_field_and_words
#print axioms active_call_feasible
end J6R11ProbeSetup
