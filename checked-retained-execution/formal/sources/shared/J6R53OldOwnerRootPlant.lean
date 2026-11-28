import J6R53OldOwnerRootEmit
import J6R21LeafOrigin

/-! Mount the paid literal gate descriptors as a complete source
roster. Every sign/opcode is checked against the localized original
Plant gate, including its old lifts, padded units, and fresh equality
columns. The emitted operand words keep their stipulated root syntax. -/
namespace J6R53OldOwnerRoot
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Leaf J6OrientedHost J6R27OriginalGate
open J6R36ChildFramedRoute J6R53OldOwner J6R25PreparedSupply J6R21Ancestor
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 2900
set_option maxHeartbeats 11000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

section Local
variable {V : Type} {own width key prec page : ℕ} {H : V→Type}
variable (gate : ∀ u, LocalGate (H u)) (suffix : ∀ u,H u→Word width)
variable (name : V→Word own) (tag : V→Origin key prec page)

def actualOwnerDesc (u : V) : LiteralOwner own width key prec page :=
  ⟨name u,tag u,List.ofFn (suffix u ∘ (gate u).port),gateHead (gate u).gate⟩

def actualOwnerValue (u : V) : OwnerData width key prec page :=
  ⟨tag u,some (encodeGate (suffix u ∘ (gate u).port) (gate u).gate)⟩

theorem actual_owner_value_exact (u : V) :
    compiledOwnerData (actualOwnerDesc gate suffix name tag u)=actualOwnerValue gate suffix tag u := by
  have code (G : LocalGate (H u)) :
      literalCode (List.ofFn (suffix u ∘ G.port)) (gateHead G.gate)=
        encodeGate (suffix u ∘ G.port) G.gate := by
    rcases G with ⟨d,ports,G⟩
    cases G <;> rfl
  exact congrArg (fun compiled=>OwnerData.mk (tag u) (some compiled)) (code (gate u))

theorem literal_bytes_give_complete_roster (order : List V)
    (descriptors : Meter (List (LiteralOwner own width key prec page)))
    (actual : descriptors.result=order.map (actualOwnerDesc gate suffix name tag)) :
    (emitLiteralRoster descriptors.result).result=
      order.map (fun u=>⟨name u,actualOwnerValue gate suffix tag u⟩) := by
  rw [actual,literal_roster_emit_exact]
  dsimp only
  rw [List.map_map]
  apply List.map_congr_left
  intro u _
  change RefRow.mk (name u) (compiledOwnerData (actualOwnerDesc gate suffix name tag u))=_
  rw [actual_owner_value_exact]

def mountLiteralSource (order : List V) (unique : order.Nodup) (all : ∀ u,u∈order)
    (desc : Meter (List (LiteralOwner own width key prec page)))
    (actual : desc.result=order.map (actualOwnerDesc gate suffix name tag)) :
    Meter (CompleteRoster name (actualOwnerValue gate suffix tag)) :=
  let paid := emitLiteralRoster desc.result
  ⟨⟨order,unique,all,paid.result,literal_bytes_give_complete_roster gate suffix name tag order desc actual⟩,
    desc.steps+paid.steps⟩

theorem mounted_literal_source_owner_exact (order : List V) (unique : order.Nodup) (all : ∀ u,u∈order)
    (desc : Meter (List (LiteralOwner own width key prec page)))
    (actual : desc.result=order.map (actualOwnerDesc gate suffix name tag))
    (inj : Function.Injective name) (u : V) :
    let R := mountLiteralSource gate suffix name tag order unique all desc actual
    (locate (name u) R.result.raw).result=some (actualOwnerValue gate suffix tag u) ∧
      R.steps=desc.steps+(3+(desc.result.map (fun x=>ownerEmitFee x+4)).sum) := by
  let R := mountLiteralSource gate suffix name tag order unique all desc actual
  refine ⟨complete_owner_hit R.result inj u,?_⟩
  exact congrArg (fun k=>desc.steps+k) (congrArg Meter.steps (literal_roster_emit_exact desc.result))

end Local

section ActualPlant
variable {S V : Type} [LinearOrder S] {a b m n ell own width key prec page : ℕ}
variable (T : Plant V m n) (w : Fin a→S)
local notation "R" => (PlantNode (b:=b) (l:=ell) T w)
local notation "H" => (fun u : R=>PlantPorts T w u)

abbrev plantGateDesc (name : R→Word own) (tag : R→Origin key prec page)
    (suffix : ∀ u,H u→Word width) : R→LiteralOwner own width key prec page :=
  actualOwnerDesc (originalPortGate T w) suffix name tag

abbrev plantGateValue (tag : R→Origin key prec page) (suffix : ∀ u,H u→Word width) :
    R→OwnerData width key prec page :=
  actualOwnerValue (originalPortGate T w) suffix tag

theorem paid_actual_Plant_gate_roster
    (name : R→Word own) (tag : R→Origin key prec page)
    (suffix : ∀ u,H u→Word width)
    (order : List R) (unique : order.Nodup) (all : ∀ u,u∈order)
    (desc : Meter (List (LiteralOwner own width key prec page)))
    (actual : desc.result=order.map (plantGateDesc T w name tag suffix))
    (inj : Function.Injective name) (u : R) :
    let out := mountLiteralSource (originalPortGate T w) suffix name tag order unique all desc actual
    (locate (name u) out.result.raw).result=some (plantGateValue T w tag suffix u) ∧
      out.steps=desc.steps+(3+(desc.result.map (fun x=>ownerEmitFee x+4)).sum) :=
  mounted_literal_source_owner_exact (originalPortGate T w) suffix name tag order unique all desc actual inj u
end ActualPlant

#print axioms actual_owner_value_exact
#print axioms literal_bytes_give_complete_roster
#print axioms mounted_literal_source_owner_exact
#print axioms paid_actual_Plant_gate_roster
end J6R53OldOwnerRoot
