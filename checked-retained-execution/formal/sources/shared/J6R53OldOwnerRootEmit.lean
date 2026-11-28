import J6R53OldOwnerTape
import J6R27OriginalGateRun

/-! Compile gate bytes from literal signs/opcode and actual ordered
suffix operands, not from an already supplied CodeGate. A bracketed
empty clause and a free gate remain distinct. -/
namespace J6R53OldOwnerRoot
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost
open J6R21Ancestor J6R21Leaf J6OrientedHost J6R27OriginalGate J6R36ChildFramedRoute
open J6R53OldOwner J6R25PreparedSupply
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 2600
set_option maxHeartbeats 7800000
set_option Elab.async false

inductive GateHead where
  | clause (signs : List Bool)
  | equal
  | free

def gateHead {d : ℕ} : Gate d→GateHead
  | .clause signs=>.clause (List.ofFn signs)
  | .equal=>.equal
  | .free=>.free

def literalCode {w : ℕ} (ports : List (Word w)) : GateHead→CodeGate (Word w)
  | .clause signs=>.clause ports signs
  | .equal=>.equal ports
  | .free=>.free

def compileGateHead {w : ℕ} (ports : List (Word w)) : GateHead→Meter (CodeGate (Word w))
  | .clause signs=>
    let p := copyGateKeys ports
    let s := copyBytes signs
    ⟨.clause p.result s.result,p.steps+s.steps+6⟩
  | .equal=>
    let p := copyGateKeys ports
    ⟨.equal p.result,p.steps+5⟩
  | .free=>⟨.free,2⟩

theorem compile_gate_head_exact {w : ℕ} (ports : List (Word w)) (head : GateHead) :
    compileGateHead ports head=⟨literalCode ports head,gateCopyFee (literalCode ports head)⟩ := by
  cases head with
  | clause signs=>simp only [compileGateHead,literalCode,gateCopyFee,copy_gate_keys_exact,copyBytes_exact]
  | equal=>simp only [compileGateHead,literalCode,gateCopyFee,copy_gate_keys_exact]
  | free=>rfl

theorem literal_leaf_gate_exact {w d : ℕ} (port : Fin d→Word w) (gate : Gate d) :
    compileGateHead (List.ofFn port) (gateHead gate)=
      ⟨encodeGate port gate,gateCopyFee (encodeGate port gate)⟩ := by
  rw [compile_gate_head_exact]
  cases gate <;> rfl

theorem retains_empty_clause {w : ℕ} :
    (compileGateHead (w:=w) [] (.clause [])).result=.clause [] [] ∧
      (runCode [] (compileGateHead (w:=w) [] (.clause [])).result).result=false ∧
      (runCode [] (compileGateHead (w:=w) [] .free).result).result=true := by
  exact ⟨rfl,rfl,rfl⟩

structure LiteralOwner (own w key prec page : ℕ) where
  name : Word own
  origin : Origin key prec page
  ports : List (Word w)
  head : GateHead

def compiledOwnerData {own w key prec page : ℕ}
    (Q : LiteralOwner own w key prec page) : OwnerData w key prec page :=
  ⟨Q.origin,some (literalCode Q.ports Q.head)⟩

def ownerEmitFee {own w key prec page : ℕ} (Q : LiteralOwner own w key prec page) : ℕ :=
  (3*own+1)+originFee key prec page Q.origin.pageKey.isSome+
    gateCopyFee (literalCode Q.ports Q.head)+7

def emitLiteralOwner {own w key prec page : ℕ} (Q : LiteralOwner own w key prec page) :
    Meter (RefRow own (OwnerData w key prec page)) :=
  let owner := copyFixed Q.name
  let tag := copyOrigin Q.origin
  let gate := compileGateHead Q.ports Q.head
  ⟨⟨owner.result,⟨tag.result,some gate.result⟩⟩,owner.steps+tag.steps+gate.steps+7⟩

theorem emit_literal_owner_exact {own w key prec page : ℕ} (Q : LiteralOwner own w key prec page) :
    emitLiteralOwner Q=⟨⟨Q.name,compiledOwnerData Q⟩,ownerEmitFee Q⟩ := by
  simp only [emitLiteralOwner,copy_fixed_exact,copy_origin_exact,compile_gate_head_exact,
    compiledOwnerData,ownerEmitFee]

def emitLiteralRoster {own w key prec page : ℕ} :
    List (LiteralOwner own w key prec page)→Meter (RawRoster own w key prec page)
  | []=>⟨[],3⟩
  | x::xs=>
    let write := emitLiteralOwner x
    let tail := emitLiteralRoster xs
    ⟨write.result::tail.result,write.steps+tail.steps+4⟩

theorem literal_roster_emit_exact {own w key prec page : ℕ} (xs : List (LiteralOwner own w key prec page)) :
    emitLiteralRoster xs=⟨xs.map (fun p=>⟨p.name,compiledOwnerData p⟩),
      3+(xs.map (fun x=>ownerEmitFee x+4)).sum⟩ := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [emitLiteralRoster,emit_literal_owner_exact,ih,List.map_cons,List.sum_cons]
    congr 1
    omega

#print axioms compile_gate_head_exact
#print axioms literal_leaf_gate_exact
#print axioms retains_empty_clause
#print axioms emit_literal_owner_exact
#print axioms literal_roster_emit_exact
end J6R53OldOwnerRoot
