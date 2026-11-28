import J6R53OldOwnerRootEmit
import J6R30GeneratedRootLayoutPorts

/-! Actual addressed reader from parsed gate heads and resident root
suffix words. The plan names original scoped wire keys; it does not
supply already compiled Gate data or any suffix words. -/
namespace J6R53OldOwnerRoot
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R53OldOwner J6R30GeneratedRootLayout J6R36ChildFramedRoute
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 2800
set_option maxHeartbeats 9500000
set_option Elab.async false

inductive HeadChoice (bound : ℕ) where
  | old (index : A1R10.Word bound)
  | equal
  | forceZero
  | free

def selectHead {bound : ℕ} (heads : List GateHead) : HeadChoice bound→Meter (Option GateHead)
  | .old index=>seekRecord index.val heads
  | .equal=>⟨some .equal,2⟩
  | .forceZero=>⟨some (.clause [false]),4⟩
  | .free=>⟨some .free,2⟩

structure OwnerPlan (own rank wire key prec page : ℕ) where
  addr : Word own
  origin : Origin key prec page
  header : HeadChoice rank
  scopes : List (Word wire)

/-- Share references to the resident suffix words until the literal
owner writer copies each actual operand into the claimed roster. -/
def readScope {wire width : ℕ} (bank : List (RefRow wire (Word width))) :
    List (Word wire)→Meter (Option (List (Word width)))
  | []=>⟨some [],3⟩
  | x::xs=>
    let q := locate x bank
    match q.result with
    | none=>⟨none,q.steps+3⟩
    | some p=>
      let rest := readScope bank xs
      ⟨rest.result.map (p::·),q.steps+rest.steps+4⟩

theorem read_scope_exact {V : Type} {wire width : ℕ}
    (bank : List (RefRow wire (Word width))) (keys : V→Word wire)
    (suffix : V→Word width) (xs : List V)
    (hit : ∀ x∈xs,(locate (keys x) bank).result=some (suffix x)) :
    readScope bank (xs.map keys)=⟨some (xs.map suffix),
      3+(xs.map (fun x=>(locate (keys x) bank).steps+4)).sum⟩ := by
  induction xs with
  | nil=>rfl
  | cons a as ih =>
    have q := hit a List.mem_cons_self
    have tail := ih (fun v hv=>hit v (List.mem_cons_of_mem a hv))
    simp only [readScope,List.map_cons,q,tail,Option.map_some,List.sum_cons]
    congr 1
    omega

def prepareLiteral {own rank wire width key prec page : ℕ}
    (heads : List GateHead) (bank : List (RefRow wire (Word width)))
    (P : OwnerPlan own rank wire key prec page) : Meter (Option (LiteralOwner own width key prec page)) :=
  let Q := selectHead heads P.header
  match Q.result with
  | none=>⟨none,Q.steps+3⟩
  | some head =>
    let s := readScope bank P.scopes
    ⟨s.result.map (fun ports=>⟨P.addr,P.origin,ports,head⟩),Q.steps+s.steps+5⟩

theorem prepare_literal_exact {own rank wire width key prec page : ℕ}
    (heads : List GateHead) (bank : List (RefRow wire (Word width)))
    (P : OwnerPlan own rank wire key prec page)
    (head : GateHead) (suffix : List (Word width))
    (header : (selectHead heads P.header).result=some head)
    (scope : (readScope bank P.scopes).result=some suffix) :
    prepareLiteral heads bank P=
      ⟨some ⟨P.addr,P.origin,suffix,head⟩,(selectHead heads P.header).steps+(readScope bank P.scopes).steps+5⟩ := by
  unfold prepareLiteral
  dsimp only
  rw [header]
  dsimp only
  rw [scope]
  rfl

def prepareLiteralBatch {own rank wire width key prec page : ℕ}
    (heads : List GateHead) (bank : List (RefRow wire (Word width))) :
    List (OwnerPlan own rank wire key prec page)→Meter (Option (List (LiteralOwner own width key prec page)))
  | []=>⟨some [],3⟩
  | x::xs=>
    let r := prepareLiteral heads bank x
    match r.result with
    | none=>⟨none,r.steps+4⟩
    | some p=>
      let tail := prepareLiteralBatch heads bank xs
      ⟨tail.result.map (p::·),r.steps+tail.steps+4⟩

theorem prepare_literal_batch_exact {V : Type} {own rank wire width key prec page : ℕ}
    (heads : List GateHead) (bank : List (RefRow wire (Word width)))
    (planned : V→OwnerPlan own rank wire key prec page)
    (decoded : V→LiteralOwner own width key prec page) (order : List V)
    (fits : ∀ u∈order,(prepareLiteral heads bank (planned u)).result=some (decoded u)) :
    prepareLiteralBatch heads bank (order.map planned)=
      ⟨some (order.map decoded),3+(order.map (fun u=>(prepareLiteral heads bank (planned u)).steps+4)).sum⟩ := by
  induction order with
  | nil=>rfl
  | cons u us ih=>
    have value := fits u List.mem_cons_self
    have t := ih (fun x hx=>fits x (List.mem_cons_of_mem u hx))
    simp only [List.map_cons,prepareLiteralBatch,value,t,Option.map_some,List.sum_cons]
    congr 1
    omega

def acquireLiteralBatch {own rank wire width key prec page : ℕ}
    (heads : Meter (List GateHead)) (bank : Meter (List (RefRow wire (Word width))))
    (plans : Meter (List (OwnerPlan own rank wire key prec page))) :
    Meter (Option (List (LiteralOwner own width key prec page))) :=
  let run := prepareLiteralBatch heads.result bank.result plans.result
  ⟨run.result,heads.steps+bank.steps+plans.steps+run.steps+5⟩

#print axioms read_scope_exact
#print axioms prepare_literal_exact
#print axioms prepare_literal_batch_exact
end J6R53OldOwnerRoot
