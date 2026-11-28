import J6R54ExteriorOwnerRoles
import J6R68ActiveInputsProducer
import J6R62LeafReader

/-! The actual greedy program already emits a complete owner label
tape (not merely edge incidences). A single lockstep pass over those
resident labels and the same ordered names produces the grouped tape
from their native coordinate, without unpacking the whole key space. -/
namespace J6R94HeldOwnerProvider
open scoped Classical
open AOracleMachineTime J6R15ModeCost J6R25PreparedSupply J6R26DescriptorTree
open J6R27OriginalGate J6R31RootResidentTables J6R49SourceLayout J6R54ExteriorOwner J6R14LayoutCost J6R68ActiveInputs
open J6R12CollisionEdges J6R12CollisionGreedyStep J6R12CollisionSource
open J6R10Repack V8NativeMessage.N2DLabels
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11000000
set_option Elab.async false

theorem chosen_greedy_output_preserves_complete_vertex_words
    {E R C : Type*} [Fintype E] {a : ℕ} {N : Network E R C}
    (I : Full64Input N a) (W : Ingress I) (q : ℕ) :
    (runWithIngress I q W).result.vertexLabels=I.run.result.2 := by
  unfold runWithIngress Full64Input.run packGreedy
  rw [W.commands,W.incidences]

def writeCurrentGroupHeaders {own : ℕ} (axis : List Bool) :
    List (Word own)→List (List Bool)→Meter (Option (List (OwnerGroup own)))
  | [],[]=>⟨some [],3⟩
  | x::xs,l::ls=>
    let k := copyFixed x
    let g := emitRoleGroup axis (.padding l)
    let tail := writeCurrentGroupHeaders axis xs ls
    ⟨tail.result.map (fun rem=>⟨k.result,g.result⟩::rem),k.steps+g.steps+tail.steps+6⟩
  | _,_=>⟨none,3⟩

def groupHeaderUnit (own axisLength : ℕ) : ℕ :=
  (3*own+1)+(16*axisLength+35+(fitWord 6 []).steps+5)+6

theorem complete_group_headers_from_exact_words
    {U : Type*} {a own : ℕ} (i : Fin a) (axis : List Bool) (fit : axis.length=i.val)
    (xs : List U) (key : U→Word own) (label : U→Fin a→Fin 64) :
    let out := writeCurrentGroupHeaders axis (xs.map key) (xs.map (fun v=>coordinateLabel (label v)))
    out.result=some (xs.map (fun v=>⟨key v,word ((label v) i).val⟩)) ∧
      out.steps≤3+xs.length*groupHeaderUnit own axis.length := by
  induction xs with
  | nil => simp [writeCurrentGroupHeaders]
  | cons v vs ih =>
    let tail := writeCurrentGroupHeaders axis (vs.map key) (vs.map (fun v=>coordinateLabel (label v)))
    let b := (emitRoleGroup axis (.padding (coordinateLabel (label v)))).steps
    have h := emit_role_group_at_coord i axis fit (label v)
    have fee := emit_role_group_cost_bound axis (.padding (coordinateLabel (label v)))
    have next := ih.2
    change tail.steps≤_ at next
    dsimp only [List.map_cons,writeCurrentGroupHeaders]
    rw [copy_fixed_exact,h,ih.1]
    refine ⟨rfl,?_⟩
    change (3*own+1)+b+tail.steps+6≤3+(vs.length+1)*groupHeaderUnit own axis.length
    have one : (3*own+1)+b+6≤groupHeaderUnit own axis.length := by
      unfold groupHeaderUnit
      change b≤_ at fee
      omega
    calc
      _=(3*own+1)+b+6+tail.steps := by omega
      _≤groupHeaderUnit own axis.length+(3+vs.length*groupHeaderUnit own axis.length) :=
        Nat.add_le_add one next
      _=3+(vs.length+1)*groupHeaderUnit own axis.length := by rw [Nat.add_mul,one_mul]; omega

#print axioms chosen_greedy_output_preserves_complete_vertex_words
#print axioms complete_group_headers_from_exact_words
end J6R94HeldOwnerProvider