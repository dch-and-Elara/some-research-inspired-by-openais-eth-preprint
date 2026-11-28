import J1R43LiteralPrinted


set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6600000
set_option maxRecDepth 2000
set_option maxSynthPendingDepth 18
set_option linter.unusedSectionVars false

/-! Source J1 end point: the reserve, conditional primitive assignment,
copy rank, and typed native exceptional row all refer to one graph-only
constructed layout. Cost here is not acquisition of a full native jet. -/
namespace J1R43Literal
open scoped Polynomial BigOperators
open J1PhysicalHost J1PhysicalCertificate J1PhysicalIndependent J1PhysicalIncidence
open J1MainSourcePlacement J1MainSourceBridge MainProbe MainClonedCNF
open J1R14Query J1PPrinted J1PhysicalPrinted DiagonalAbundance
noncomputable section

section Contract
variable {I S X C P : Type*} [Fintype I] [DecidableEq I] [Fintype S] [LinearOrder S]
    [Fintype X] [DecidableEq X] [Fintype C] [Fintype P] [DecidableEq P]

structure ExactNativeJ1 (D : DiagonalLayout I S X C P) (J : Finset ℕ) (h0 : 0∉J) : Prop where
  /-- Actual copied integer read from the primitive display, restricted
  to the same original group. -/
  integerRow :
    ∀ t g (p : P), (D.slot p).2 t=g → ∀ x : X→Bool,
      rowRead D (printedBasis D J h0) t g (D.copy p,(printedBasis D J h0).diagonalIndex p) x =
        if x (D.pinVar p) then 1 else 0
  /-- A feasible address fixes this bit; an empty fibre does not supply
  a private point by fiat. -/
  fibrePin :
    ∀ t g (E : Finset X) (y : RowValues S C (Exceptional I S J)) (x : X→Bool),
      x∈secondScan D (printedBasis D J h0) t g E y →
      ∀ p : P, (D.slot p).2 t=g → x (D.pinVar p)=prescribed D (printedBasis D J h0) t y p
  /-- The original unary factor is the Boolean bit test as a polynomial
  identity, valid at every Taylor order and for every U. -/
  pinPolynomial :
    ∀ t g (E : Finset X) (y : RowValues S C (Exceptional I S J)) (x U : X→Bool),
      x∈secondScan D (printedBasis D J h0) t g E y →
      ∀ (p : P), (D.slot p).2 t=g → ∀ (s : Bool) (f : ℚ[X]) (node : I→ℚ),
        pinFactor s (correctedArgument (sourceRow f node (D.slot p)) (node t)
          (embedded D (D.copy p) (fun j => boolRat (x j)))
          (embedded D (D.copy p) (fun j => boolRat (U j)))) =
          if s=prescribed D (printedBasis D J h0) t y p then 1 else 0
  groupZero :
    ∀ t g (E : Finset X) (y : RowValues S C (Exceptional I S J))
      (U : X→Bool) (sign : P→Bool) (f : ℚ[X]) (node : I→ℚ) (other : (X→Bool)→ℚ[X]),
      ∀ p∈ownedPins D t g Finset.univ, sign p≠prescribed D (printedBasis D J h0) t y p →
        sourceGroupProbe D J f node t g Finset.univ
          (secondScan D (printedBasis D J h0) t g E y) U (prescribed D (printedBasis D J h0) t y)
          sign other=0

theorem receive_exact_native_J1
    (D : DiagonalLayout I S X C P) (J : Finset ℕ) (h0 : 0∉J) :
    ExactNativeJ1 D J h0 := by
  let basis := printedBasis D J h0
  constructor
  · exact rowRead_diagonal D basis
  · exact prescribed_of_fibre D basis
  · intro t g E y x U hx p hg s f node
    rw [correctedArgument_pin,prescribed_of_fibre D basis t g E y x hx p hg,pinFactor_on_bit]
  · intro t g E y U sign f node other p hp hwrong
    exact sourceGroupProbe_off D J h0 f node t g Finset.univ
      (secondScan D basis t g E y) U (prescribed D basis t y) sign other p hp hwrong

end Contract

section Source
variable {B : Type*} [Fintype B] [DecidableEq B]

/-- The concrete printed instance; any fixed graph enumeration is allowed.
The same output that appears inside the score receipt reaches the native
row tests, including on groups where the original address has no points. -/
theorem actual_checked_native (M : Match B) (b : B) (beta : ℕ)
    (hScale : 32≤mainScaleIndex (printedLambda B)) (hBeta : beta+3≤mainScaleIndex (printedLambda B)+1)
    (special : Site B) (default : Symbol B)
    (vertices : List (Vertex B)) (allVertices : ∀ v, v∈vertices)
    (keys : List (ConfigKey M (Site B))) (keyNodup : keys.Nodup) (allKeys : ∀ k,k∈keys)
    (ports : List (Port (edges M))) (allPorts : ∀ e,e∈ports) :
    let H := reserveRun M b vertices ∅
    let z := selected M special H keys (List.finRange (sourceR (printedLambda B))) default
    let D := printableLayout M special H z.1 ports allPorts
    let J := pubInterval (I:=Site B) (S:=Symbol B) (mainRadius beta (printedLambda B))
    originalPrintedScore M special H z.1<2 ∧
      (∀ i g, sourceMu H (Site B) (Symbol B)/2 <
        ((ownedPins D i g Finset.univ).card:ℚ)) ∧
      ∃ h0 : 0∉J, ExactNativeJ1 D J h0 := by
  obtain ⟨_,_,_,hs,_,_,hits,h0,_⟩ :=
    checked_original_J1_layout M b beta hScale hBeta special default vertices allVertices
      keys keyNodup allKeys ports allPorts
  dsimp only
  exact ⟨hs,hits,⟨h0,receive_exact_native_J1 _ _ h0⟩⟩

end Source

#print axioms ExactNativeJ1
#print axioms receive_exact_native_J1
#print axioms actual_checked_native

end
end J1R43Literal