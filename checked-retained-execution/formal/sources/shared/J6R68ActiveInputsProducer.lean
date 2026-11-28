import J6R68ActiveInputsBudget

/-! Concrete metered binding for the selected call. The incidence and
vertex command inputs come from one already named physical meter.
We pay that meter once, plus the original collision/export routine. -/
namespace J6R68ActiveInputs
open scoped Classical Polynomial
open AOracleMachineTime AOracleMachineTimeTape J6R10Repack P11FullPacking
open J6R12CollisionEdges J6R12CollisionMenu J6R12CollisionSource J6R12CollisionGreedyStep
open J6R11CollisionReindex J6R14LayoutCost J6R17ModeTape
open J6ActiveRun J6R9Recursive J6R11Blueprint J6R12Blueprint J1PPrinted
open V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13500000
set_option maxRecDepth 3300
set_option Elab.async false

abbrev IngressBytes := List Target × List (List Bool×List Bool)

structure Ingress {E R C : Type*} [Fintype E] {a : ℕ}
    {N : Network E R C} (I : Full64Input N a) where
  paid : Meter IngressBytes
  commands : paid.result.1=I.order.map I.format.target
  incidences : paid.result.2=I.raw

section Physical
variable {E R C : Type*} [Fintype E] {a : ℕ}
variable {N : Network E R C} (I : Full64Input N a) (P : PhysicalPacking N a (Fin 64))

def runWithIngress (q : ℕ) (W : Ingress I) : Meter GreedyPackedTape :=
  let F := I.format
  let g := packGreedy a F.e F.kR F.kC F.b q W.paid.result.1 W.paid.result.2
  ⟨g.result,W.paid.steps+g.steps+3⟩

theorem ingress_run_is_actual_export (q : ℕ) (W : Ingress I) :
    let g := runWithIngress I q W
    let F := paidFixedOutput I q
    g.result.boxes=F.result.boxes ∧ g.result.copies=F.result.copies ∧
      g.steps=W.paid.steps+F.steps+3 := by
  dsimp only [runWithIngress]
  rw [W.commands,W.incidences]
  exact ⟨rfl,rfl,rfl⟩

def paidSelectedSetup (q : ℕ) (hq : 0<q) (ha : a≤q)
    (fit : Fintype.card E<2^q) (coord : ∀ w,I.format.label w=coordinateLabel w)
    (caught : I.run.result.1=I.format.graph (fun v=>some (wordsOf P v)))
    (rounded : RoundsExactly P) (W : Ingress I) :
    Meter (LayoutReceipt a P.copies (q+1) (Fintype.card E)) :=
  let actual := runWithIngress I q W
  let h := fixed_export_of_same_paid_labels I P q hq ha fit coord caught rounded
  let x := ingress_run_is_actual_export I q W
  ⟨⟨actual.result.boxes,⟨actual.result.copies,(congrArg List.length x.2.1).trans h.1⟩,
    by change bitsValue actual.result.copies=P.copies; rw [x.2.1]; exact h.2.1,
    x.1.symm ▸ h.2.2.1,x.1.symm ▸ h.2.2.2.1,x.1.symm ▸ h.2.2.2.2.1⟩,actual.steps⟩

variable [Fintype R] [Fintype C]

theorem physical_layout_setup_has_uniform_fee (q K : ℕ) (hq : 0<q) (ha : a≤q)
    (fit : Fintype.card E<2^q) (coord : ∀ w,I.format.label w=coordinateLabel w)
    (caught : I.run.result.1=I.format.graph (fun v=>some (wordsOf P v)))
    (rounded : RoundsExactly P) (W : Ingress I) (nativeFee : I.run.steps≤I.fee)
    (S : LayoutScales I q K) (slots : 2^a*J9PrintedSchedule.arrayCard a≤Fintype.card E) :
    let pay := paidSelectedSetup I P q hq ha fit coord caught rounded W
    pay.result.copies.bits=(runWithIngress I q W).result.copies ∧
      pay.steps≤W.paid.steps+selectedLayoutRoof K+3 := by
  refine ⟨rfl,?_⟩
  change (runWithIngress I q W).steps≤_
  rw [(ingress_run_is_actual_export I q W).2.2]
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (paid_same_selection_layout_upper I P q K hq ha fit coord caught rounded nativeFee S slots) _) _
end Physical

noncomputable section
variable {f : ℤ[X]} {ell s : ℕ} {c : Call (PhysicalHost f ell)}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s)
  (J6ActiveRun.Call.depth c))
local instance liveEdges : Fintype c.host.Edge := c.host.finiteEdge
local instance liveRows : Fintype c.host.Row := c.host.finiteRow
local instance liveCols : Fintype c.host.Col := c.host.finiteCol

theorem layout_actual_edge_count (d : Ready SP (sourceDelta s) c) :
    Fintype.card c.host.Edge=c.edges := by
  rw [←Nat.card_eq_fintype_card]
  exact (J6R11Repack.host_card c.host).trans d.edgeCount

end
#print axioms ingress_run_is_actual_export
#print axioms physical_layout_setup_has_uniform_fee
#print axioms layout_actual_edge_count
end J6R68ActiveInputs
