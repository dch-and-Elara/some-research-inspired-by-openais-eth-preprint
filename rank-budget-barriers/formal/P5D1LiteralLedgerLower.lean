import P5D1LiteralLedger
import P5D1LiteralPrinted

/-! Printed visit lower bound for the literal root ledger, not for an
unrestricted calculator or a native instruction/bit-time meter. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun
  J6R12Blueprint J6R10Reachable J6R9Recursive J6R9PacketScopes
  P11FullPacking Paper5.HybridClosure J1PPrinted J6R12Integral
  GraphCutMoments
open Paper5.HybridClosure.Printed (dLambda printedExponent)

variable {V : Type} [Fintype V] [DecidableEq V] [Nonempty V]
variable (E : Finset (V × V)) (reg₀ : ∀ v,degree E v=3) (loop₀ : ∀ v,(v,v)∉E)
variable (f : ℤ[X])
local notation "F" => replacedEdges E reg₀
local notation "reg" => replaced_cubic E reg₀ loop₀
local notation "Ws" => Fintype.card (TriVertex V)
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => (oldRowRoot F reg f (fun _ => false))

theorem printed_D1_literal_visits
    (hdeg : f.natDegree = 4*dLambda Ws)
    (hsize : (2*epsDen)^30*(3:ℕ)^10 ≤ dLambda Ws)
    (hf : f.Monic) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (γ : ℚ) (hg : 0<γ) (hg₃ : γ≤3)
    (expand : ∀ U : Finset V, γ*(min U.card (Fintype.card V-U.card):ℕ)≤
      ((boundary E U).card:ℚ))
    (hr : Paper5.HybridClosure.Printed.Ready γ Ws) :
    ∃ (P : RootPacking F reg f) (d : Ready S Δ r*),
      ∀ σ : TriVertex V→Bool,
        2^(printedExponent γ Ws) ≤ (rootVisitLedger F reg f P d hf σ).length := by
  obtain ⟨P,d,hmin,_⟩ := original_printed_D1_finite E reg₀ loop₀ f hdeg hsize hf γ hg hg₃ expand hr
  refine ⟨P,d,fun σ => ?_⟩
  exact hmin.trans (FixedSchedule.card_le_trace_length (literalRootProductTrace F reg f P d hf σ))

#print axioms printed_D1_literal_visits
end Paper5.D1Literal
