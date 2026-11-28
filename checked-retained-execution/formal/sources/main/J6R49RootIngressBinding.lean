import J6R49RootIngressAssembly
import J6R37StructuredRootEmitBase

/-! The paid ingress is consumed by the exact immutable parent file
selected by R37. This keeps the old compact file identity, physical
chart and original occurrence and never re-packs to a different order. -/
namespace J6R49RootIngress
open scoped Classical Polynomial
open Polynomial Std.Sat J6OrientedHost J6Mesh J6R24LegalLayout J6R26StablePreparedRoot
open J6R30GeneratedRootLayout J6R32RootGeneratedRegistryInputs J6R34RootAtlas
open J6R37StructuredRoot J6R25PreparedSupply AOracleMachineTime J7R10Ports J7R10Plant
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 13000000
set_option maxRecDepth 3900
set_option quotPrecheck false

def buildParentIngress {r c d h : ℕ} (m : ℕ) (declares : List (List Bool))
    (raw : BitsCNF) (pos : List (Position r c d h)) :
    Meter (Option (List (PortRow (rootHalfWidth m)))) :=
  let a := compileRootIngress declares raw pos
  match a.result with
  | none => ⟨none,a.steps+3⟩
  | some raw =>
    let b := makeHalfTape m [] raw
    ⟨some b.result,a.steps+b.steps+5⟩

variable {V : Type} [DecidableEq V] [Fintype V]
variable (F : CNF V) (code : V→List Bool) (inj : Function.Injective code)
variable {f : ℤ[X]} {base native : ℕ}
noncomputable abbrev CNFShape (F : CNF V) (f : ℤ[X]) (base native : ℕ) :=
  RootShape f (J7R10Readout.mCNF F) (printedHalf (J7R10Readout.mCNF F)) base native
    (printedRankWidth (J7R10Readout.mCNF F)) (physicalPlant (guarded F))
    (J6R28GeneratedRootFrame.constantRootWord (J7R10Readout.mCNF F))

variable {G : CNFShape F f base native}
variable {ell q r c d edgew tc tj key prec tw bw h : ℕ}
variable (X : StableExterior G ell q r c d edgew tc tj key prec tw bw)
variable (pos : List (Position r c d h))
variable (chart : pos=List.ofFn (positionForWire (guarded F) X.source.codec))
local notation "m" => J7R10Readout.mCNF F
local notation "keys" => ((Finset.univ : Finset V).toList.map code)
local notation "raw" => codeCNF code F

include inj chart in
theorem actual_compact_input_is_generated (fit : (guarded F).length≤2^h) :
    (compileRootIngress keys raw pos).result=some X.source.raw := by
  obtain ⟨new,H,E⟩ := paid_compact_root_ingress F code inj X.source.codec fit pos chart
  rw [H,new.exactFile,X.source.exactFile,E]

include inj chart in
theorem actual_structured_root_from_ingress (fit : (guarded F).length≤2^h) :
    let run := buildParentIngress m keys raw pos
    run.result=some (rootParent X).raw ∧
      (rootParent X).raw.length=2*M m ∧
      run.steps≤(compileRootIngress keys raw pos).steps+halfTapeFee m r c d+5 := by
  have compact := actual_compact_input_is_generated F code inj X pos chart fit
  have old := generated_typed_parent_receipt G X.source ell X.centre
  dsimp only [buildParentIngress]
  rw [compact]
  exact ⟨congrArg some old.1.symm,old.2.1,by
    change _+(makeHalfTape m [] X.source.raw).steps+5≤_
    exact Nat.add_le_add_right (Nat.add_le_add_left old.2.2 _) _⟩

#print axioms actual_compact_input_is_generated
#print axioms actual_structured_root_from_ingress
end J6R49RootIngress
