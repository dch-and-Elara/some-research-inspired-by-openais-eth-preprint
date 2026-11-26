import P5D1LiteralProgram
import J6R12IntegralDirectPrinted

/-! The R12 printed physical blueprint supplies the local source
certificate used by the D1 field expression. These are its generated
recursive replies, on the original finite receiving data. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial
open Polynomial J6ActiveRun J6R9Recursive J6R10Reachable J6R12Blueprint
open J6R11Blueprint J1PPrinted J6R12Integral

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell))
local notation "S₀" => (printedParams (f:=f) (ell:=ell) s)
local notation "Δ₀" => sourceDelta s
local notation "N₀" => shape S₀ Δ₀ sel
local notation "Ch₀" => children S₀ Δ₀ sel
local notation "PS" => paddedShape N₀ Ch₀ r

variable [envDec : DecidableEq (Envelope N₀ Ch₀ r)]

set_option maxHeartbeats 16000000 in
omit envDec in
include cfg in
theorem printed_physical_field_menu_integral
    (seed : Stable s C r) (hf : f.Monic) (hF : 0 < f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] (ha : (S₀).cutoff < r.edges) :
    let B := J6R12Blueprint.sourceBlueprint sel r hf
    ∃ (fit : ProofFit PS f r) (out : IntRing f ell),
      embed f ell out =
        nativeFieldMenuSum PS f ell r fit (fun w => B.program.run (B.program.child r w)) ∧
      (2 : IntRing f ell)^r.prec ∣ out - r.host.contract hf := by
  dsimp only
  let B := J6R12Blueprint.sourceBlueprint sel r hf
  let D : B.SourceSpec := actualSourceSpec S₀ Δ₀ sel r (printedGuards cfg sel r seed) hf
  have hc : D.Valid r := NativeReach.reflexive _
  have hp : (PS).cutoff < r.edges := ha
  obtain ⟨out,hout,hd⟩ := program_field_menu_integral B D hf hF r hc hp
  refine ⟨D.fit r hc hp,out,hout,?_⟩
  rwa [physicalBlueprint_truth hf B rfl r seed.edgeCount] at hd

#print axioms printed_physical_field_menu_integral
end Paper5.D1Literal

