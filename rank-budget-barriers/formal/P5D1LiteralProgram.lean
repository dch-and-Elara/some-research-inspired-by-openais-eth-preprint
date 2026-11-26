import P5D1LiteralTerminal
import J6R9RecursiveRun

/-! The responses fed to the D1 linear menu can be the verified recursive
program itself, not an oracle. The remaining SourceSpec is the exact
physical source certificate, not a hypothesis about the final output. -/
namespace Paper5.D1Literal
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive

variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
variable {S : Shape Host Mode} {f : ℤ[X]} {ell : ℕ}

set_option maxHeartbeats 9500000 in
theorem program_field_menu_integral
    (B : Blueprint S f ell) (D : B.SourceSpec)
    (hf : f.Monic) (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (c : Call Host) (hc : D.Valid c) (ha : S.cutoff < c.edges) :
    ∃ out : IntRing f ell, embed f ell out =
      nativeFieldMenuSum S f ell c (D.fit c hc ha) (fun w => B.program.run (B.program.child c w)) ∧
      (2 : IntRing f ell)^c.prec ∣ out - B.truth c := by
  have eq : (fun w : Address S c => B.program.run (B.program.child c w)) =
      (fun w : Address S c => B.expect (B.program.child c w)) := by
    funext w
    exact B.run_exact D hf hF _ (D.child_valid c hc ha w)
  rw [eq]
  exact native_field_menu_integral S f hf hF ell c (D.fit c hc ha)
    (D.taper c hc ha).1 (D.taper c hc ha).2 (D.deformation c) (D.degree c hc ha)
    (D.jets c) (fun t ht => D.integral c hc ha ⟨t,ht⟩) (B.truth c) (D.origin c hc ha)
    _ (D.grouped c hc ha)

#print axioms program_field_menu_integral
end Paper5.D1Literal

