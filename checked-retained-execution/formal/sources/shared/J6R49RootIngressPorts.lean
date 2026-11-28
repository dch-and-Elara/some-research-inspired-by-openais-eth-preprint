import J6R49RootIngressGuard
import J6R30GeneratedRootLayoutReceipt

/-! Compile the compact signed R30 ingress file from the real guarded
syntax and an explicit *position-only* atlas of the old physical order.
The atlas contains no polarity bits. Its row, leg, subdivision and side
are the frozen chart, not a newly chosen, allegedly identical order. -/
namespace J6R49RootIngress
open scoped Classical
open Std.Sat J6OrientedHost J7R10Ports J7R10Plant A1R10 AOracleMachineTime AOracleMachineTimeTape
open J6R30GeneratedRootLayout
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 9600000
set_option maxRecDepth 2900

structure Position (r c d h : ℕ) where
  row : A1R10.Word r
  column : A1R10.Word c
  leg : A1R10.Word d
  side : Bool
  clause : Option (A1R10.Word h)

def wordAt (w a : ℕ) : A1R10.Word w := ⟨encodeBits w a,encodeBits_length _ _⟩

def flagFromSyntax {r c d h : ℕ} (syntaxRows : BitsCNF) (a : Position r c d h) :
    Meter (Option OldFlag) :=
  match a.clause with
  | none => ⟨some .equal,4⟩
  | some i =>
    let x := seekRecord i.val syntaxRows
    match x.result with
    | none => ⟨none,x.steps+5⟩
    | some row =>
      let y := seekRecord a.leg.val row
      ⟨y.result.map (fun p => OldFlag.literal p.2),x.steps+y.steps+8⟩

def signPosition {r c d h : ℕ} (rows : BitsCNF) (a : Position r c d h) :
    Meter (Option (SignedHalfPort r c d)) :=
  let q := flagFromSyntax rows a
  match q.result with
  | none => ⟨none,q.steps+4⟩
  | some flag =>
    let x := copySeed ⟨a.row,a.column,a.leg,a.side,flag⟩
    ⟨some x.result,q.steps+x.steps+6⟩

theorem sign_position_fee {r c d h : ℕ} (rows : BitsCNF) (a : Position r c d h)
    (k : ℕ) (width : ∀ c∈rows,c.length≤k) :
    (signPosition rows a).steps ≤ 22+rows.length*(10*h+8)+k*(10*d+8)+seedFee r c d := by
  have b : (flagFromSyntax rows a).steps ≤ 16+rows.length*(10*h+8)+k*(10*d+8) := by
    cases hw : a.clause with
    | none => simp only [flagFromSyntax,hw]; omega
    | some key =>
      have bx := (seek_record_exact key.val rows).2
      rw [key.property] at bx
      cases hx : (seekRecord key.val rows).result with
      | none => simp only [flagFromSyntax,hw,hx]; omega
      | some row =>
        have hit : row∈rows := by
          have receipt := (seek_record_exact key.val rows).1
          rw [hx] at receipt
          exact List.mem_of_getElem? receipt.symm
        have by0 := (seek_record_exact a.leg.val row).2
        rw [a.leg.property] at by0
        have hy := by0.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (width row hit)) 4)
        simp only [flagFromSyntax,hw,hx]
        omega
  unfold signPosition
  cases hs : (flagFromSyntax rows a).result <;> simp only [hs,seed_copy_exact] <;> omega

noncomputable def actualPosition {V : Type*} [DecidableEq V] [Fintype V]
    (H : CNF V) {r c d h : ℕ} (C : LiteralCodec (physicalPlant H) r c d)
    (x : OldPort H) (y : Fin (nSubdiv H)×Bool) : Position r c d h :=
  ⟨C.rowCode x.1,wordAt c y.1.val,wordAt d x.2.val,y.2,
    match x.1 with | .inl i => some (wordAt h i.val) | .inr _ => none⟩

theorem find_coded_clause {V : Type*} (H : CNF V) (code : V→List Bool) (h : ℕ)
    (fit : H.length≤2^h) (i : J7R9Compiler.ClauseIndex H) :
    (seekRecord (wordAt h i.val).val (codeCNF code H)).result =
      some ((H.get i).map (codeLit code)) := by
  rw [(seek_record_exact _ _).1]
  change (codeCNF code H)[bitsValue (encodeBits h i.val)]?=_
  rw [encodeBits_exact _ _ (i.isLt.trans_le fit)]
  simp [codeCNF,List.getElem?_eq_getElem,i.isLt]

theorem find_coded_literal {V : Type*} (row : CNF.Clause V) (code : V→List Bool) (d : ℕ)
    (fit : row.length≤2^d) (j : Fin row.length) :
    (seekRecord (wordAt d j.val).val (row.map (codeLit code))).result =
      some (codeLit code (row.get j)) := by
  rw [(seek_record_exact _ _).1]
  change (row.map (codeLit code))[bitsValue (encodeBits d j.val)]?=_
  rw [encodeBits_exact _ _ (j.isLt.trans_le fit)]
  simp [List.getElem?_eq_getElem,j.isLt]

theorem sign_actual_position {V : Type*} [DecidableEq V] [Fintype V]
    (H : CNF V) (code : V→List Bool) {r c d h : ℕ}
    (C : LiteralCodec (physicalPlant H) r c d) (fit : H.length≤2^h)
    (x : OldPort H) (y : Fin (nSubdiv H)×Bool) :
    (signPosition (codeCNF code H) (actualPosition H C x y : Position r c d h)).result =
      some ⟨C.rowCode x.1,wordAt c y.1.val,wordAt d x.2.val,y.2,flagAt (gate H x.1) x.2⟩ := by
  rcases x with ⟨i|v,j⟩
  · have hfit : (H.get i).length≤2^d := C.portFit (.inl i)
    have hi := find_coded_clause H code h fit i
    have hj := find_coded_literal (H.get i) code d hfit j
    simp only [signPosition,flagFromSyntax,actualPosition,hi,hj,Option.map_some,codeLit,
      flagAt, gate, J7R9Compiler.literal,seed_copy_exact]
  · simp [signPosition,flagFromSyntax,actualPosition,flagAt,gate,seed_copy_exact]

noncomputable def positionForWire {V : Type*} [DecidableEq V] [Fintype V]
    (H : CNF V) {r c d h : ℕ} (C : LiteralCodec (physicalPlant H) r c d) (u : Fin (nWires H)) :
    Position r c d h :=
  actualPosition H C ((physicalPlant H).rowPort.symm u) ((physicalPlant H).colPort.symm u)

theorem sign_wire_exact {V : Type*} [DecidableEq V] [Fintype V]
    (H : CNF V) (code : V→List Bool) {r c d h : ℕ}
    (C : LiteralCodec (physicalPlant H) r c d) (fit : H.length≤2^h) (u : Fin (nWires H)) :
    (signPosition (codeCNF code H) (positionForWire H C u : Position r c d h)).result =
      some (plantHalfPort (physicalPlant H) C u) :=
  sign_actual_position H code C fit _ _

#print axioms sign_position_fee
#print axioms find_coded_clause
#print axioms find_coded_literal
#print axioms sign_actual_position
#print axioms sign_wire_exact
end J6R49RootIngress
