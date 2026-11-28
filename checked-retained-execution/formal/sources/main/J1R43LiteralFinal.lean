import J1R43LiteralNative
import J1R43LiteralCompleted
import J1R43LiteralWork
import J1R43LiteralRates
import J1R43LiteralIntegerDriver
import J1R43LiteralWordBounds
import J1R43LiteralThreshold
import J1R43LiteralRoster

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9200000
set_option maxRecDepth 2200
set_option maxSynthPendingDepth 20
set_option linter.unusedSectionVars false

/-! Condensed original J1: a fixed graph-only, bounded-word integer
chooser supplies the real physical layout used by every original
exceptional-address read. The numerical scope is the preprocessing
needed for the label/score objective, not the cost of native jet queries. -/
namespace J1R43Literal
open J1PhysicalHost J1PhysicalCertificate J1PhysicalIndependent J1PhysicalIncidence
open J1MainSourceBridge J1MainSourceCollision MainProbe MainClonedCNF DiagonalAbundance
open J1R14Query J1PhysicalPrinted J1PPrinted
noncomputable section

variable {B : Type*} [Fintype B] [DecidableEq B]

local notation "N" => Fintype.card (Vertex B)
local notation "r" => sourceR (printedLambda B)

theorem literal_original_J1_with_integer_work (M : Match B) (b : B) (beta : ℕ)
    (hScale : 32≤mainScaleIndex (printedLambda B)) (hBeta : beta+3≤mainScaleIndex (printedLambda B)+1)
    (special : Site B) (default : Symbol B)
    (vertices : List (Vertex B)) (allVertices : ∀ v,v∈vertices)
    (keys : List (ConfigKey M (Site B))) (keyNodup : keys.Nodup) (allKeys : ∀ k,k∈keys)
    (ports : List (Port (edges M))) (allPorts : ∀ e,e∈ports) :
    let H := reserveRun M b vertices ∅
    let z := chooseLayoutInt (sourceIntegerScore M special H) (List.finRange r) default keys (fun _=>none)
    let D := printableLayout M special H z.1 ports allPorts
    let J := pubInterval (I:=Site B) (S:=Symbol B) (mainRadius beta (printedLambda B))
    H ⊆ available M b ∧ Independent M H ∧ N≤4*H.card+6 ∧
      originalPrintedScore M special H z.1<2 ∧
      (∀ c,load ((physicalData M special z.1).cell) c <
        2*((Fintype.card (Port (edges M)):ℚ)/(Fintype.card (Draw (Site B) (Symbol B)):ℚ))) ∧
      (∀ i g,load (fun v : Variable (Vertex B) => J1MainSourceLabels.variableWord z.1 v i) g <
        2*((Fintype.card (Variable (Vertex B)):ℚ)/(Fintype.card (Symbol B):ℚ))) ∧
      (∀ i g, sourceMu H (Site B) (Symbol B)/2 <
        ((ownedPins D i g Finset.univ).card:ℚ)) ∧
      (∃ h0 : 0∉J, ExactNativeJ1 D J h0) ∧
      (z.2*candidateCompletionCount M special H≤249600*N^8) ∧
      (∀ state : ConfigKey M (Site B) → Option (Symbol B),
        (sourceIntegerScore M special H state).natAbs≤19931136*N^12) := by
  letI : Nonempty B := ⟨b⟩
  letI : Nonempty (Site B) := ⟨special⟩
  letI : Nonempty (Symbol B) := ⟨default⟩
  let H := reserveRun M b vertices ∅
  have hN : 0<N := Fintype.card_pos
  obtain ⟨_,_,_,size,_,_⟩ := actual_j1_guards N beta hN hScale hBeta
  obtain ⟨sub,ind,cover,score,cells,groups,hits,outside,_⟩ :=
    checked_original_J1_layout M b beta hScale hBeta special default vertices allVertices
      keys keyNodup allKeys ports allPorts
  change N≤4*H.card+6 at cover
  have hH : 0<H.card := by omega
  have hmatch := integer_selector_is_original M special H hH keys (List.finRange r) default
  have hWork := original_conditioned_local_work M b beta hScale hBeta special default H
    keys keyNodup allKeys
  have hWords (state : ConfigKey M (Site B) → Option (Symbol B)) :=
    (original_candidate_word_bounds M b beta hScale hBeta special default H state).2
  dsimp only
  rw [show chooseLayoutInt (sourceIntegerScore M special (reserveRun M b vertices ∅))
    (List.finRange r) default keys (fun _=>none) =
      selected M special (reserveRun M b vertices ∅) keys (List.finRange r) default from hmatch]
  exact ⟨sub,ind,cover,score,cells,groups,hits,⟨outside,receive_exact_native_J1 _ _ outside⟩,hWork,hWords⟩

#print axioms literal_original_J1_with_integer_work

end
end J1R43Literal