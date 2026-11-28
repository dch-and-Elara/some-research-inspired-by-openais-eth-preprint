import J6R51IngressSerialJoin

/-! Either subsequent consumer reads the very same newly serialized
fresh chart. The meters include the parse, graph/order compilation,
all posted rank and label writes, and the selected consumer. -/
namespace J6R51Ingress
open scoped Classical
open Std.Sat A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6R49RootIngress J6R50RootIngress J6R30GeneratedRootLayout J6Mesh
open J7R9Compiler J7R9Subdivision J7R10Plant
open J6R12CollisionGreedyStep J6R14LayoutCost J6R17ModeTape J6R10Repack
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 17300000
set_option maxRecDepth 3200

def greedyFromRaw {r c d : ℕ} (a e q h j : ℕ)
    (decl : List (List Bool)) (raw : BitsCNF) :
    Meter (Option GreedyPackedTape) :=
  let P := serializeRawCNF (r:=r) (c:=c) (d:=d) h j decl raw
  match P.result with
  | none => ⟨none,P.steps+5⟩
  | some f =>
    let G := packGreedy a e r c (6*a) q f.targets f.incidence
    ⟨some G.result,P.steps+G.steps+7⟩

def mountFromRaw {r c d : ℕ} (h j : ℕ)
    (decl : List (List Bool)) (raw : BitsCNF) :
    Meter (Option (List (MountedPort r c d))) :=
  let P := serializeRawCNF (r:=r) (c:=c) (d:=d) h j decl raw
  match P.result with
  | none => ⟨none,P.steps+5⟩
  | some f =>
    let G := generatedPaddedPorts f.ports.length f.ports
    ⟨some G.result,P.steps+G.steps+7⟩

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V]
variable (F : CNF V) (s : DeclaredOrder V)
local notation "H" => guardedInOrder F s.roster

structure SerialGuards (h d j r c e : ℕ) where
  hpos : 0<h
  dpos : 0<d
  jpos : 0<j
  rpos : 0<r
  cpos : 0<c
  clausesFit : (H).length≤2^h
  rawLegFit : ∀ row∈H,row.length≤2^d
  localsFit : ∀ v,(occurrences H v).length-3≤2^j
  edgesFit : nWires H<2^e
  rowFit : Fintype.card (OrderedOld H)≤2^r
  columnFit : nSubdiv H≤2^c
  portFit : ∀ v : OrderedOld H,orderedDegree H v≤2^d

variable {h d j r c e : ℕ} (g : SerialGuards F s h d j r c e)
variable (code : V→List Bool) (inj : Function.Injective code)
local notation "S" => guardRoster s
local notation "keys" => s.roster.map code
local notation "raw" => codeCNF code F
local notation "prep" => serializeRawCNF (r:=r) (c:=c) (d:=d) h j keys raw

include g inj in
theorem actual_raw_greedy_packing (a q : ℕ)
    (hq : 0<q) (ha : a≤q) (qf : nWires H<2^q) (width : ∀ row∈H,row.length≤4)
    (collision : 2*(J9PrintedSchedule.arrayCard a)^2*4≤nWires H)
    (slots : 2^a*J9PrintedSchedule.arrayCard a≤nWires H) :
    let A := freshFormat H S a e r c g.edgesFit g.rowFit g.columnFit
    let run := greedyFromRaw (r:=r) (c:=c) (d:=d) a e q h j keys raw
    ∃ P : PhysicalPacking (freshNetwork H S) a (Fin 64),
      ∃ L : LayoutReceipt a P.copies (q+1) (Fintype.card (Fin (nWires H))),
        ∃ out : GreedyPackedTape,run.result=some out ∧
          L.boxes=out.boxes ∧ L.copies.bits=out.copies ∧
          run.steps≤(prep).steps+packGreedyCap a q A+7 := by
  let A := freshFormat H S a e r c g.edgesFit g.rowFit g.columnFit
  obtain ⟨p,Z,t,_,i⟩ := serialized_actual_fresh_input F s code inj h d j r c a e
    g.hpos g.dpos g.jpos g.rpos g.cpos g.clausesFit g.rawLegFit g.localsFit
    g.edgesFit g.rowFit g.columnFit g.portFit
  let E := packGreedy a e r c (6*a) q p.targets p.incidence
  obtain ⟨P,L,box,bits,fee⟩ := fresh_paid_greedy_packing H S a e r c q g.edgesFit
    g.rowFit g.columnFit hq ha qf width collision slots
  have same : E=packGreedy a A.e A.kR A.kC A.b q ((freshVisits H S).map A.target)
      (A.edges.map (fun u=>(encodeBits A.kR (A.rCode (A.row u)),encodeBits A.kC (A.cCode (A.col u))))) := by
    unfold E
    rw [t,i]
    rfl
  refine ⟨P,L,E.result,?_,?_,?_,?_⟩
  · dsimp only [greedyFromRaw]
    rw [Z]
  · rw [same]
    exact box
  · rw [same]
    exact bits
  · dsimp only [greedyFromRaw]
    rw [Z]
    change (prep).steps+E.steps+7≤_
    rw [same]
    exact Nat.add_le_add_right (Nat.add_le_add_left fee _) _

include g inj in
theorem actual_raw_printed_root_mount :
    let Y := mountFromRaw (r:=r) (c:=c) (d:=d) h j keys raw
    ∃ C : LiteralPortFile (freshPlant H S) r c d,
      C.codec=freshCodec H S r c d g.rowFit g.columnFit g.portFit ∧
      Y.result=some ((actualWires (nWires H)).map (trueMounted C)) ∧
      ((actualWires (nWires H)).map (trueMounted C)).length=M (nWires H) ∧
      (((actualWires (nWires H)).map (trueMounted C)).map fun row=>row.base.key).Nodup ∧
      Y.steps≤(prep).steps+paddedPortsFee (nWires H) r c d+7 := by
  obtain ⟨p,Z,_,L,_⟩ := serialized_actual_fresh_input F s code inj h d j r c 0 e
    g.hpos g.dpos g.jpos g.rpos g.cpos g.clausesFit g.rawLegFit g.localsFit
    g.edgesFit g.rowFit g.columnFit g.portFit
  let C : LiteralPortFile (freshPlant H S) r c d :=
    ⟨freshCodec H S r c d g.rowFit g.columnFit g.portFit,p.ports,L⟩
  have n : p.ports.length=nWires H := by rw [L,List.length_ofFn]
  have E := paid_fresh_root_padded_pass H S C
  have out : (generatedPaddedPorts p.ports.length p.ports).result=
      (actualWires (nWires H)).map (trueMounted C) := by
    rw [n]
    exact E.1
  refine ⟨C,rfl,?_,?_,?_,?_⟩
  · dsimp only [mountFromRaw]
    rw [Z]
    exact congrArg some out
  · rw [←E.1]
    exact E.2.1
  · rw [←E.1]
    exact E.2.2.1
  · dsimp only [mountFromRaw]
    rw [Z]
    change (prep).steps+(generatedPaddedPorts p.ports.length p.ports).steps+7≤_
    rw [n]
    exact Nat.add_le_add_right (Nat.add_le_add_left E.2.2.2 _) _

#print axioms actual_raw_greedy_packing
#print axioms actual_raw_printed_root_mount
end
end J6R51Ingress
