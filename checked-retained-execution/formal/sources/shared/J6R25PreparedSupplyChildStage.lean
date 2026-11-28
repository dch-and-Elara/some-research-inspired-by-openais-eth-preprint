import J6R25PreparedSupplyPhysicalPorts
import J6R25PreparedSupplyRegistry

/-! Actual child graph header emission and byte lookup. The payload in
this file is the serial wire-record slice, not the new entry coefficient
table or either side's complete encoding of tensor programs. -/
namespace J6R25PreparedSupply
open AOracleMachineTime J6R15ModeCost J6R21Ancestor

def rowBytes {w : ℕ} (r : PortRow w) : List Bool :=
  r.address.bits++r.group.bits++r.body

def serializeRows {w : ℕ} : List (PortRow w)→Meter (List Bool)
  | [] => ⟨[],2⟩
  | row::rows =>
    let rd := copyBytes (rowBytes row)
    let tail := serializeRows rows
    ⟨rd.result++tail.result,rd.steps+tail.steps+3*(w+6+row.body.length)+4⟩

def serializeFee {w : ℕ} (xs : List (PortRow w)) :=
  2+(xs.map (fun x=>6*(w+6+x.body.length)+5)).sum

theorem serialize_rows_exact {w : ℕ} (rows : List (PortRow w)) :
    (serializeRows rows).result=rows.flatMap rowBytes ∧
      (serializeRows rows).steps=serializeFee rows := by
  induction rows with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    constructor
    · change (copyBytes (rowBytes x)).result++(serializeRows xs).result=_
      rw [copyBytes_exact,ih.1]
      rfl
    · change (copyBytes (rowBytes x)).steps+(serializeRows xs).steps+3*(w+6+x.body.length)+4=_
      rw [copyBytes_exact,ih.2]
      simp only [rowBytes,List.length_append,x.address.size,x.group.size,serializeFee,List.map_cons,List.sum_cons]
      omega

def childStage {w b dep prec aw : ℕ} (key : Meter (Word aw)) (group : Word 6)
    (p : Word prec) (oldDepth : Word dep) (parent : List (PortRow w)) :
    Meter (DirRow aw) :=
  let graph := childPortsWithCount (b:=b) group parent
  let depth := increment oldDepth
  let bytes := serializeRows graph.result.1
  let receipt := writeChildHeader key.result p depth.result graph.result.2 bytes.result
  ⟨receipt.result,key.steps+graph.steps+depth.steps+bytes.steps+receipt.steps+6⟩

theorem child_stage_exact {w b dep prec aw : ℕ} (key : Meter (Word aw)) (group : Word 6)
    (p : Word prec) (oldDepth : Word dep) (parent : List (PortRow w)) :
    let graph := childPortsWithCount (b:=b) group parent
    let d := increment oldDepth
    let O := childStage (b:=b) key group p oldDepth parent
    O.result.id=key.result ∧
      O.result.bytes=childHeaderBytes p d.result graph.result.2 (graph.result.1.flatMap rowBytes) ∧
      O.steps=key.steps+graph.steps+d.steps+serializeFee graph.result.1+
        (6*(prec+dep+b)+3*(graph.result.1.flatMap rowBytes).length+2*aw+9)+6 := by
  let G := childPortsWithCount (b:=b) group parent
  let d := increment oldDepth
  let V := serializeRows G.result.1
  let R := writeChildHeader key.result p d.result G.result.2 V.result
  have hv := serialize_rows_exact G.result.1
  have hr := child_header_write key.result p d.result G.result.2 V.result
  change R.result.id=_ ∧ R.result.bytes=_ ∧ key.steps+G.steps+d.steps+V.steps+R.steps+6=_
  exact ⟨hr.1,hr.2.1.trans (congrArg (childHeaderBytes p d.result G.result.2) hv.1),
    by rw [hr.2.2,hv.1,hv.2]⟩

#print axioms serialize_rows_exact
#print axioms child_stage_exact
end J6R25PreparedSupply
