import J6R53OldOwnerRootPlant
import J6R53OldOwnerRootSuffix
import J6R53OldOwnerRootLoad
import J6R52CacheSourceReplay

/-! Join parsed opcode heads to the actual original root suffix bytes
over complete ordered licensed owner plans. The result is an actual
typed raw roster, not an existential choice of interpreted Gate. -/
namespace J6R53OldOwnerRoot
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor J6R21Leaf
open J6R25PreparedSupply J6R31RootResidentTables J6R30GeneratedRootLayout
open J6R32RootGeneratedRegistryInputs J6R53TerminalGate J6R24LegalLayout J6OrientedHost J6Mesh
open J6R28GeneratedRootFrame J6R10Repack J6R35RootOrigins J6R36ChildFramedRoute
open J6R53OldOwner J6R52CacheSource
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3600
set_option maxHeartbeats 18000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V] {m n r c d own rank key prec page : ℕ}
variable (P : Plant V m n)
local notation "N" => (SourceVertex P)
abbrev rootLocalGate (x : N) := originalPortGate P (constantRootWord m) x
abbrev rootOperand (x : N) (p : PlantPorts P (constantRootWord m) x) :
    Word (SuffixWordWidth m) := rootWireSuffix P (edge p.val)

def rootPlanWord (name : N→Word own) (origin : N→Origin key prec page)
    (header : N→HeadChoice rank) (v : N) :
    OwnerPlan own rank (SuffixKeyWidth m) key prec page :=
  let G := rootLocalGate P v
  ⟨name v,origin v,header v,List.ofFn (stableWireKeyWord m ∘ edge ∘ Subtype.val ∘ G.port)⟩

theorem actual_root_plan_reads_literal
    (C : LiteralPortFile P r c d) (axis : List Bool) (clock : axis.length=(oddAxis m).val)
    (name : N→Word own) (origin : N→Origin key prec page)
    (header : N→HeadChoice rank) (heads : List GateHead)
    (hit : ∀ v,(selectHead heads (header v)).result=some (gateHead (rootLocalGate P v).gate))
    (x : N) :
    (prepareLiteral heads (paidRootSuffixBank m axis C.raw).result
      (rootPlanWord P name origin header x)).result=
      some (actualOwnerDesc (rootLocalGate P) (rootOperand P) name origin x) := by
  let G := rootLocalGate P x
  let K := fun j : Fin G.degree=>stableWireKeyWord m (edge (G.port j).val)
  let S := fun j : Fin G.degree=>rootWireSuffix P (edge (G.port j).val)
  let bank := (paidRootSuffixBank m axis C.raw).result
  let B := rootPlanWord P name origin header x
  let X := actualOwnerDesc (rootLocalGate P) (rootOperand P) name origin x
  have all (j : Fin G.degree) (_ : j∈List.ofFn (fun j : Fin G.degree=>j)) :
      (locate (K j) bank).result=some (S j) := actual_suffix_bank_covers_original_wire C axis clock _
  have ports := congrArg Meter.result
    (read_scope_exact bank K S (List.ofFn (fun j : Fin G.degree=>j)) all)
  have got : (readScope bank B.scopes).result=some X.ports := by
    simp only [List.map_ofFn,Function.comp_def] at ports
    exact ports
  have head : (selectHead heads B.header).result=some X.head := hit x
  have h := prepare_literal_exact heads bank B X.head X.ports head got
  exact congrArg Meter.result h

theorem acquired_root_literal_batch_exact
    (C : LiteralPortFile P r c d) (axis : List Bool) (clock : axis.length=(oddAxis m).val)
    (name : N→Word own) (origin : N→Origin key prec page)
    (header : N→HeadChoice rank) (heads : Meter (List GateHead))
    (hit : ∀ v,(selectHead heads.result (header v)).result=some (gateHead (rootLocalGate P v).gate))
    (order : List N) (plans : Meter (List (OwnerPlan own rank (SuffixKeyWidth m) key prec page)))
    (exactPlan : plans.result=order.map (rootPlanWord P name origin header)) :
    (acquireLiteralBatch heads (paidRootSuffixBank m axis C.raw) plans).result=
      some (order.map (actualOwnerDesc (rootLocalGate P) (rootOperand P) name origin)) := by
  unfold acquireLiteralBatch
  dsimp only
  rw [exactPlan,prepare_literal_batch_exact]
  intro u _
  exact actual_root_plan_reads_literal P C axis clock name origin header heads.result hit u

def mountSourceFromParsedHeads
    (C : LiteralPortFile P r c d) (axis : List Bool) (clock : axis.length=(oddAxis m).val)
    (name : N→Word own) (origin : N→Origin key prec page)
    (header : N→HeadChoice rank) (heads : Meter (List GateHead))
    (hit : ∀ v,(selectHead heads.result (header v)).result=some (gateHead (rootLocalGate P v).gate))
    (order : List N) (unique : order.Nodup) (all : ∀ u,u∈order)
    (plans : Meter (List (OwnerPlan own rank (SuffixKeyWidth m) key prec page)))
    (exactPlan : plans.result=order.map (rootPlanWord P name origin header)) :
    Meter (CompleteRoster name (actualOwnerValue (rootLocalGate P) (rootOperand P) origin)) :=
  let batch := acquireLiteralBatch heads (paidRootSuffixBank m axis C.raw) plans
  have value := acquired_root_literal_batch_exact P C axis clock name origin header heads hit order plans exactPlan
  let data := unwrapSuccess batch (by
    change (acquireLiteralBatch heads (paidRootSuffixBank m axis C.raw) plans).result.isSome
    rw [value]
    rfl)
  mountLiteralSource (rootLocalGate P) (rootOperand P) name origin order unique all data
    (congrArg Meter.result (unwrap_success_exact _ _ _ value))

theorem mounted_root_Plant_contains_actual_owner
    (C : LiteralPortFile P r c d) (axis : List Bool) (clock : axis.length=(oddAxis m).val)
    (name : N→Word own) (origin : N→Origin key prec page)
    (header : N→HeadChoice rank) (heads : Meter (List GateHead))
    (hit : ∀ v,(selectHead heads.result (header v)).result=some (gateHead (rootLocalGate P v).gate))
    (order : List N) (unique : order.Nodup) (all : ∀ u,u∈order)
    (plans : Meter (List (OwnerPlan own rank (SuffixKeyWidth m) key prec page)))
    (exactPlan : plans.result=order.map (rootPlanWord P name origin header))
    (inj : Function.Injective name) (u : N) :
    let out := mountSourceFromParsedHeads P C axis clock name origin header heads hit order unique all plans exactPlan
    (locate (name u) out.result.raw).result=some (actualOwnerValue (rootLocalGate P) (rootOperand P) origin u) :=
  complete_owner_hit (mountSourceFromParsedHeads P C axis clock name origin header heads hit order unique all plans exactPlan).result inj u

#print axioms actual_root_plan_reads_literal
#print axioms acquired_root_literal_batch_exact
#print axioms mountSourceFromParsedHeads
#print axioms mounted_root_Plant_contains_actual_owner
end
end J6R53OldOwnerRoot
