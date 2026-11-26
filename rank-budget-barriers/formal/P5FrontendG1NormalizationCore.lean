import P5FrontendG1Literal

/-! The actual source normalization of a family of clauses as literal sets,
and the exact eligibility predicate of its sparsification root. No unit
propagation, variable elimination, or equation hashing occurs here. -/
namespace Paper5.FrontendG1.Normalization

abbrev ClauseSet (W : Type*) := Finset (W × Bool)
abbrev Family (W : Type*) := Finset (ClauseSet W)

variable {W : Type*} [DecidableEq W]

def parsed (f : Std.Sat.CNF W) : Family W :=
  f.toFinset.image List.toFinset

theorem mem_parsed (f : Std.Sat.CNF W) (C : ClauseSet W) :
    C ∈ parsed f ↔ ∃ L ∈ f, List.toFinset L = C := by
  simp [parsed]

def TautFree (C : ClauseSet W) : Prop :=
  ∀ w, (w,true) ∈ C → (w,false) ∉ C

/-- The source treats a clause as a set. Repeated literals and clauses were
removed by `parsed`; delete tautologies, then proper supersets. -/
noncomputable def normalize (F : Family W) : Family W := by
  classical
  let G := F.filter TautFree
  exact G.filter fun C => ¬∃ D ∈ G, D ⊂ C

theorem mem_normalize (F : Family W) (C : ClauseSet W) :
    C ∈ normalize F ↔
      C ∈ F ∧ TautFree C ∧ ¬∃ D ∈ F, TautFree D ∧ D ⊂ C := by
  classical
  simp only [normalize, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hm,ht⟩,hn⟩
    refine ⟨hm,ht,?_⟩
    rintro ⟨D,hD,hTd,hs⟩
    exact hn ⟨D,⟨hD,hTd⟩,hs⟩
  · rintro ⟨hm,ht,hn⟩
    refine ⟨⟨hm,ht⟩,?_⟩
    rintro ⟨D,⟨hD,hTd⟩,hs⟩
    exact hn ⟨D,hD,hTd,hs⟩

theorem normalization_fixed (F : Family W)
    (tf : ∀ C ∈ F, TautFree C)
    (anti : ∀ C ∈ F, ∀ D ∈ F, C ⊆ D → C = D) :
    normalize F = F := by
  ext C
  rw [mem_normalize]
  refine ⟨And.left, fun hC => ⟨hC,tf C hC,?_⟩⟩
  rintro ⟨D,hD,_,hs⟩
  exact hs.ne (anti D hD C hC hs.subset)

noncomputable def degShared (F : Family W) (c : ℕ) (H : ClauseSet W) : ℕ := by
  classical
  exact (F.filter fun C => C.card = c ∧ H ⊆ C).card

def SplitEligible (M : ℕ) (F : Family W) : Prop :=
  ∃ C ∈ F, ∃ H : ClauseSet W, H.Nonempty ∧ H ⊂ C ∧
    M^(C.card-H.card) ≤ degShared F C.card H

inductive RootAction (W : Type*)
  | contradiction
  | noClauses
  | split
  | leaf (f : Family W)

/-- These are precisely the root outcomes needed to certify a single leaf.
The source's deterministic tie-breaking is immaterial when no split is legal. -/
noncomputable def sourceRoot (M : ℕ) (F : Family W) : RootAction W := by
  classical
  let G := normalize F
  exact if ∅ ∈ G then .contradiction else if G = ∅ then .noClauses
    else if SplitEligible M G then .split else .leaf G

theorem sourceRoot_unsplit (M : ℕ) (F : Family W)
    (hnorm : normalize F = F) (h0 : ∅ ∉ F)
    (hne : F.Nonempty) (hSplit : ¬SplitEligible M F) :
    sourceRoot M F = .leaf F := by
  classical
  simp [sourceRoot, hnorm, h0, Finset.nonempty_iff_ne_empty.mp hne, hSplit]

#print axioms mem_parsed
#print axioms mem_normalize
#print axioms normalization_fixed
#print axioms sourceRoot_unsplit
end Paper5.FrontendG1.Normalization