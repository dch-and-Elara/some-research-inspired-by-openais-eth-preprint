import J6R11Small

namespace J6R11SourceReady
open scoped Classical Polynomial
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J1PPrinted
open NativeProbeRing J6R11ProbeSetup J6R11Threshold

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
variable {Values : ℕ → Type*} {s : ℕ} {W : Call Host → ℤ → Mode → ℕ}

/-- The source's root choice of a probe field suffices on every genuinely
reachable active call. The threshold witnesses are computed from s and C;
the theorem does not make a fit assertion on irrelevant fabricated calls. -/
theorem one_root_field_all_calls (P : Program (printedShape s W) Values)
    (root : Call Host) (hroot : root.depth = 0)
    (C : ℕ) (hC : 0 < C) (seed : root.edges ≤ C*s)
    (hsize : J6R11Small.threshold C ≤ Nat.clog 2 s) :
    ∃ f : ℤ[X], f.Monic ∧ f.natDegree = 4*Nat.clog 2 s ∧ Irreducible (residuePoly f) ∧
      (∃ words : Fin (2^(4*Nat.clog 2 s)) → Fin f.natDegree → Bool,
        words ⟨0,pow_pos (by decide) _⟩ = (fun _ => false) ∧
        ∀ p, 0 < p →
          probe p f (words ⟨0,pow_pos (by decide) _⟩)=0 ∧
          ∀ i j, i≠j → IsUnit (probe p f (words j)-probe p f (words i))) ∧
      ∀ c, Reach P root c → (printedShape s W).cutoff < c.edges →
        ProofFit (printedShape s W) f c ∧
        (1 ≤ (printedShape s W).levelWidth c.depth ∧
          (printedShape s W).levelWidth c.depth ≤ (printedShape s W).levelBits c.depth ∧
          (printedShape s W).levelWidth c.depth ≤ c.edges) ∧
        let L := 2^(printedShape s W).levelBits c.depth
        let D := stepD (Nat.clog 2 s) c.depth
        2*D^2*sourceDelta s ≤ c.edges ∧ L*D ≤ c.edges ∧ 2*L ≤ sourceDelta s := by
  obtain ⟨hs,hCs,hU⟩ := printed_size_implies_numeric_guards s C hC hsize
  obtain ⟨f,hf,hdeg,hirr,hwords⟩ := shared_field_and_words s hs
  refine ⟨f,hf,hdeg,hirr,hwords,fun c hc ha => ?_⟩
  exact active_call_feasible P root c hc hroot C hC hCs seed hU hsize ha f hdeg

#print axioms one_root_field_all_calls
end J6R11SourceReady
