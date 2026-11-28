import J1R43LiteralPhysical
import J1R43LiteralReads
import J1PPrintedMain

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5800000
set_option maxRecDepth 1800
set_option maxSynthPendingDepth 18
set_option linter.unusedSectionVars false

/-! Exact original MAIN sizes, one graph-only conditional chooser and one
stable physical export. The retained count assertions refer to the same
literal copy address as the exceptional-basis read interface. -/
namespace J1R43Literal
open scoped BigOperators
open J1PhysicalHost J1PhysicalCertificate J1PhysicalAccepted
open J1PhysicalIndependent J1PhysicalIncidence
open J1MainSourcePlacement J1MainSourceBridge J1MainSourceCollision
open J1R14Query MainProbe MainClonedCNF DiagonalAbundance
open J1PhysicalPrinted J1PPrinted
noncomputable section

variable {B : Type*} [Fintype B] [DecidableEq B]

abbrev printedLambda (B : Type*) [Fintype B] := Nat.clog 2 (4*Fintype.card (Vertex B))
abbrev Site (B : Type*) [Fintype B] := Fin (sourceQ (printedLambda B))
abbrev Symbol (B : Type*) [Fintype B] := Fin (sourceR (printedLambda B))

def printableLayout (M : Match B) (t : Site B) (H : Finset (Vertex B))
    (cfg : ConfigKey M (Site B) → Symbol B)
    (ports : List (Port (edges M))) (allPorts : ∀ e, e∈ports) :=
  stableLayout (physicalData M t cfg) (literalPortOrder ports allPorts) ports allPorts (pinSubset M H)

theorem same_physical_owned_counts (M : Match B) (t : Site B)
    (H : Finset (Vertex B)) (cfg : ConfigKey M (Site B) → Symbol B)
    (ports : List (Port (edges M))) (allPorts : ∀ e, e∈ports) (i : Site B) (g : Symbol B) :
    (ownedPins (printableLayout M t H cfg ports allPorts) i g Finset.univ).card =
      (ownedPins (compiledLayout (physicalData M t cfg) (pinSubset M H)) i g Finset.univ).card := by
  rw [printableLayout,owned_stable_equals_hits]
  unfold compiledLayout
  rw [owned_card_hits]

theorem checked_original_J1_layout (M : Match B) (b : B) (beta : ℕ)
    (hScale : 32≤mainScaleIndex (printedLambda B))
    (hBeta : beta+3≤mainScaleIndex (printedLambda B)+1)
    (special : Site B) (default : Symbol B)
    (vertices : List (Vertex B)) (allVertices : ∀ v, v∈vertices)
    (keys : List (ConfigKey M (Site B))) (keyNodup : keys.Nodup) (allKeys : ∀ k,k∈keys)
    (ports : List (Port (edges M))) (allPorts : ∀ e,e∈ports) :
    let H := reserveRun M b vertices ∅
    let z := selected M special H keys (List.finRange (sourceR (printedLambda B))) default
    let D := printableLayout M special H z.1 ports allPorts
    H ⊆ available M b ∧ Independent M H ∧ Fintype.card (Vertex B)≤4*H.card+6 ∧
    originalPrintedScore M special H z.1<2 ∧
    (∀ c, load ((physicalData M special z.1).cell) c <
      2*((Fintype.card (Port (edges M)):ℚ)/(Fintype.card (Draw (Site B) (Symbol B)):ℚ))) ∧
    (∀ i g, load (fun v : Variable (Vertex B) => J1MainSourceLabels.variableWord z.1 v i) g <
      2*((Fintype.card (Variable (Vertex B)):ℚ)/(Fintype.card (Symbol B):ℚ))) ∧
    (∀ i g, sourceMu H (Site B) (Symbol B) / 2 <
      ((ownedPins D i g Finset.univ).card:ℚ)) ∧
    0 ∉ pubInterval (I:=Site B) (S:=Symbol B) (mainRadius beta (printedLambda B)) ∧
    z.2 = 2*keys.length*sourceR (printedLambda B) := by
  letI : Nonempty B := ⟨b⟩
  letI : Nonempty (Site B) := ⟨special⟩
  letI : Nonempty (Symbol B) := ⟨default⟩
  have hN : 0<Fintype.card (Vertex B) := Fintype.card_pos
  obtain ⟨hr,hR,hQ,hs,hC,hG⟩ :=
    actual_j1_guards (Fintype.card (Vertex B)) beta hN hScale hBeta
  let P := List.finRange (sourceR (printedLambda B))
  have hp : ∀ g : Symbol B, g ∈ P := by intro g; simp [P]
  have hs' : 192*Fintype.card (Site B)*Fintype.card (Symbol B)^2*
      Fintype.card (Symbol B)^Fintype.card (Site B)+6 < Fintype.card (Vertex B) := by
    simpa only [Fintype.card_fin] using hs
  have hC' : 10*(Fintype.card (Symbol B)^(2*Fintype.card (Site B)))^2≤
      12*Fintype.card (Vertex B) := by simpa only [Fintype.card_fin] using hC
  have hG' : 2*Fintype.card (Site B)*Fintype.card (Symbol B)^2≤4*Fintype.card (Vertex B) := by
    simpa only [Fintype.card_fin] using hG
  obtain ⟨sub,ind,cover,score,cells,groups,hits,fee⟩ := conditioned_graph_layout M b special
    vertices allVertices keys keyNodup allKeys P hp default hs' hC' hG'
  have hz : 0∉pubInterval (I:=Site B) (S:=Symbol B) (mainRadius beta (printedLambda B)) :=
    zero_not_mem_printedInterval (by simpa only [Fintype.card_fin] using hr) hR
      (by simpa only [Fintype.card_fin] using hQ)
  dsimp only
  refine ⟨sub,ind,cover,score,cells,groups,?_,hz,?_⟩
  · intro i g
    rw [same_physical_owned_counts]
    exact hits i g
  · simpa only [P,List.length_finRange] using fee

#print axioms same_physical_owned_counts
#print axioms checked_original_J1_layout

end
end J1R43Literal