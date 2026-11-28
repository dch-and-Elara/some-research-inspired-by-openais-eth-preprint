import J6R49SourceLayoutOwners
import J6R27OriginalGateRun

/-! Raw owner records are not inferred from a half-port. Original
gate bytes (including a genuinely zero-arity gate) and inherited
native Page origins have their own separately read payload. -/
namespace J6R53OldOwner
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost
open J6R21Ancestor J6R27OriginalGate J6R36ChildFramedRoute J6R25PreparedSupply
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 2200
set_option maxHeartbeats 6000000
set_option Elab.async false

structure OwnerData (gate key prec page : ℕ) where
  origin : Origin key prec page
  gateCode : Option (CodeGate (Word gate))

def copyGateKeys {w : ℕ} : List (Word w)→Meter (List (Word w))
  | []=>⟨[],3⟩
  | a::as=>
    let one := copyFixed a
    let other := copyGateKeys as
    ⟨one.result::other.result,one.steps+other.steps+4⟩

theorem copy_gate_keys_exact {w : ℕ} (keys : List (Word w)) :
    copyGateKeys keys=⟨keys,3+(3*w+5)*keys.length⟩ := by
  induction keys with
  | nil=>rfl
  | cons a as ih =>
    simp only [copyGateKeys,copy_fixed_exact,ih,List.length_cons,Nat.mul_succ]
    congr 1
    omega

def gateCopyFee {w : ℕ} : CodeGate (Word w)→ℕ
  | .free=>2
  | .equal keys=>3+(3*w+5)*keys.length+5
  | .clause keys signs=>3+(3*w+5)*keys.length+(3*signs.length+1)+6

def copyGateCode {w : ℕ} : CodeGate (Word w)→Meter (CodeGate (Word w))
  | .free=>⟨.free,2⟩
  | .equal keys=>
    let K := copyGateKeys keys
    ⟨.equal K.result,K.steps+5⟩
  | .clause keys signs=>
    let K := copyGateKeys keys
    let S := copyBytes signs
    ⟨.clause K.result S.result,K.steps+S.steps+6⟩

theorem copy_gate_code_exact {w : ℕ} (G : CodeGate (Word w)) :
    copyGateCode G=⟨G,gateCopyFee G⟩ := by
  cases G with
  | free=>rfl
  | equal keys=>simp only [copyGateCode,copy_gate_keys_exact,gateCopyFee]
  | clause keys signs=>
    simp only [copyGateCode,copy_gate_keys_exact,copyBytes_exact,gateCopyFee]

def optGateFee {w : ℕ} : Option (CodeGate (Word w))→ℕ
  | none=>2
  | some G=>gateCopyFee G+4

def copyOptGate {w : ℕ} : Option (CodeGate (Word w))→Meter (Option (CodeGate (Word w)))
  | none=>⟨none,2⟩
  | some G=>
    let done := copyGateCode G
    ⟨some done.result,done.steps+4⟩

theorem copy_opt_gate_exact {w : ℕ} (G : Option (CodeGate (Word w))) :
    copyOptGate G=⟨G,optGateFee G⟩ := by
  cases G <;> simp only [copyOptGate,optGateFee,copy_gate_code_exact]

def ownerDataFee {gate key prec page : ℕ} (x : OwnerData gate key prec page) : ℕ :=
  originFee key prec page x.origin.pageKey.isSome+optGateFee x.gateCode+5

def copyOwnerData {gate key prec page : ℕ} (x : OwnerData gate key prec page) :
    Meter (OwnerData gate key prec page) :=
  let tag := copyOrigin x.origin
  let G := copyOptGate x.gateCode
  ⟨⟨tag.result,G.result⟩,tag.steps+G.steps+5⟩

theorem copy_owner_data_exact {gate key prec page : ℕ} (x : OwnerData gate key prec page) :
    copyOwnerData x=⟨x,ownerDataFee x⟩ := by
  cases x
  simp only [copyOwnerData,copy_origin_exact,copy_opt_gate_exact,ownerDataFee]

abbrev RawRoster (own gate key prec page : ℕ) := List (RefRow own (OwnerData gate key prec page))

def paidOwnerLookup {own gate key prec page : ℕ} (rows : RawRoster own gate key prec page)
    (k : Word own) : Meter (Option (OwnerData gate key prec page)) :=
  let h := locate k rows
  match h.result with
  | none=>⟨none,h.steps+3⟩
  | some rec =>
    let op := copyOwnerData rec
    ⟨some op.result,h.steps+op.steps+4⟩

theorem paid_owner_lookup_exact {own gate key prec page : ℕ} (rows : RawRoster own gate key prec page)
    (k : Word own) (a : OwnerData gate key prec page) (eq : (locate k rows).result=some a) :
    paidOwnerLookup rows k=⟨some a,(locate k rows).steps+ownerDataFee a+4⟩ := by
  unfold paidOwnerLookup
  dsimp only
  rw [eq]
  dsimp only
  rw [copy_owner_data_exact]

#print axioms copy_gate_keys_exact
#print axioms copy_gate_code_exact
#print axioms copy_opt_gate_exact
#print axioms copy_owner_data_exact
#print axioms paid_owner_lookup_exact
end J6R53OldOwner
