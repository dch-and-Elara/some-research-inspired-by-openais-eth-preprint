import J6R9RecursiveAssemble
import J6ChildPlan

/-! The complete recursive proof uses the concrete active assembly rather
than assuming the active equation. Remaining source obligations concern
only the finite parent deformation, child packing, and equality of a
single grouped probe to its source value. Leaves directly enumerate the
literal Boolean edge coordinates. No bit complexity or executable
subroutine for finding physical packings is claimed here. -/
namespace J6R9Recursive
open scoped BigOperators Polynomial
open Polynomial J6ActiveRun J6ActiveSchedule J6ActiveUniqueness J6ActivePrintedHermite

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]

structure Blueprint (S : Shape Host Mode) (f : ℤ[X]) (ell : ℕ) where
  childHost : ∀ c, Address S c → Host
  childEdges : ∀ c, Address S c → ℕ
  edgeBound : ∀ c, S.cutoff < c.edges → ∀ w, 32 * childEdges c w ≤ 3 * c.edges
  /-- The list of individually retained or newly created tensor entries,
  read on the same Boolean edge assignment. -/
  entries : ∀ c : Call Host, (Fin c.edges → Bool) → List (IntRing f ell)

variable {S : Shape Host Mode} {f : ℤ[X]} {ell : ℕ}

noncomputable def Blueprint.truth (B : Blueprint S f ell) (c : Call Host) : IntRing f ell :=
  ∑ x : Fin c.edges → Bool, (B.entries c x).prod

noncomputable def Blueprint.leaf (B : Blueprint S f ell) (c : Call Host) : Box f ell c.prec :=
  J6ChildPlan.allBits c.edges (fun x => reduce c.prec f ell (B.entries c x).prod)

theorem Blueprint.leaf_exact (B : Blueprint S f ell) (c : Call Host) :
    B.leaf c = reduce c.prec f ell (B.truth c) := by
  rw [Blueprint.leaf,J6ChildPlan.allBits_exact,Blueprint.truth,map_sum]

noncomputable def Blueprint.program (B : Blueprint S f ell) : Program S (Box f ell) where
  childHost := B.childHost
  childEdges := B.childEdges
  edgeBound := B.edgeBound
  leaf := B.leaf
  assemble := fun c answers =>
    if fit : ProofFit S f c then J6R9Recursive.assemble S f ell c fit answers else 0

noncomputable def Blueprint.expect (B : Blueprint S f ell) (c : Call Host) : Box f ell c.prec :=
  reduce c.prec f ell (B.truth c)

structure Blueprint.SourceSpec (B : Blueprint S f ell) where
  /-- Genuine generated calls, not arbitrary raw records with unrestricted edge counts. -/
  Valid : Call Host → Prop
  child_valid : ∀ c, Valid c → S.cutoff < c.edges → ∀ w,
    Valid (B.program.child c w)
  deformation : Call Host → (RatRing f ell)[X]
  jets : Call Host → ℤ → (IntRing f ell)[X]
  fit : ∀ c, Valid c → S.cutoff < c.edges → ProofFit S f c
  taper : ∀ c, Valid c → S.cutoff < c.edges → 0 < S.levelWidth c.depth ∧ S.levelWidth c.depth ≤ c.edges
  degree : ∀ c, Valid c → S.cutoff < c.edges →
    (deformation c).natDegree ≤ J9PrintedSchedule.degreeBound c.edges (2^S.levelBits c.depth)
  integral : ∀ c, Valid c → S.cutoff < c.edges → ∀ (t : Center S c),
    (jets c t.val).map (embed f ell) =
      atNode (dyadicUnit (S.levelBits c.depth)) (t.val:RatRing f ell) (deformation c)
  origin : ∀ c, Valid c → S.cutoff < c.edges → (deformation c).eval 0 = embed f ell (B.truth c)
  grouped : ∀ c (hc : Valid c) (h : S.cutoff < c.edges) (t : Center S c) (z : Probe S c),
    groupedSample S f ell c (fun w => B.expect (B.program.child c w)) t z =
      ((jets c t.val).map (reduce (registerPrecision S c t) f ell)).eval
        (sampleNode S f ell c (fit c hc h) t z)

theorem Blueprint.active_exact (B : Blueprint S f ell) (D : B.SourceSpec)
    (hf : f.Monic) (hF : 0 < f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (c : Call Host) (hc : D.Valid c) (h : S.cutoff < c.edges) :
    B.program.assemble c (fun w => B.expect (B.program.child c w)) = B.expect c := by
  simp only [Blueprint.program, dif_pos (D.fit c hc h)]
  change assemble S f ell c (D.fit c hc h) (fun w => B.expect (B.program.child c w)) = _
  exact assemble_exact S f hf hF ell c (D.fit c hc h)
    (D.taper c hc h).1 (D.taper c hc h).2 (D.deformation c) (D.degree c hc h) (D.jets c)
    (fun t ht => D.integral c hc h ⟨t,ht⟩) (B.truth c) (D.origin c hc h) _ (D.grouped c hc h)

/-- Exact semantic execution at every generated depth using the actual
finite receiving rings and printed count of probes, modes and groups.
The hypotheses are local source certificates, not a recursive answer
oracle, and in particular do not assume the active equation. The common
finite Mode alphabet is part of the blueprint: an instantiation must
justify its code envelope and any dummy-mode cancellation in grouped. -/
theorem Blueprint.run_exact (B : Blueprint S f ell) (D : B.SourceSpec)
    (hf : f.Monic) (hF : 0 < f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] (c : Call Host) (hc : D.Valid c) :
    B.program.run c = reduce c.prec f ell (B.truth c) := by
  rw [Program.run]
  split
  · exact B.leaf_exact c
  · rename_i hn
    have ha : S.cutoff < c.edges := Nat.lt_of_not_ge hn
    have eq : (fun w : Address S c => B.program.run (B.program.child c w)) =
        (fun w : Address S c => B.expect (B.program.child c w)) := by
      funext w
      exact B.run_exact D hf hF _ (D.child_valid c hc ha w)
    rw [eq]
    exact B.active_exact D hf hF c hc ha
termination_by c.edges
decreasing_by exact B.program.child_smaller c ha w

#print axioms Blueprint.leaf_exact
#print axioms Blueprint.active_exact
#print axioms Blueprint.run_exact
end J6R9Recursive