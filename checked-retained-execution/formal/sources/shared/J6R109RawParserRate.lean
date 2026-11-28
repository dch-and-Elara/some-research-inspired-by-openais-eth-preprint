import J6R109PhysicalFrame

namespace J6R109RawParserRate
open AOracleMachineTime A1R10 J6R49RootIngress J6R51Ingress J6R50RootIngress
open J6R109PhysicalFrame
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 16000000

theorem map_sum_le_constant {A : Type*} (xs : List A) (cost : A → ℕ) (bound : ℕ)
    (fit : ∀ x∈xs,cost x≤bound) : (xs.map cost).sum≤xs.length*bound := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have a := fit x List.mem_cons_self
    have b := ih (fun y hy=>fit y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def clauseParserRoof (h d width size : ℕ) : ℕ :=
  tapeFee d size+5+size*(16+4*(h+d+width))

theorem leased_clause_fees_are_from_the_read_literal_bytes {h d : ℕ}
    (k : Word h) (row : BitsClause) (width size : ℕ)
    (hsize : row.length≤size) (hwidth : ∀ lit∈row,lit.1.length≤width) :
    let R := parseClause (d:=d) k row
    R.result.length≤size ∧ R.steps≤clauseParserRoof h d width size := by
  let L := indexTape d row.length
  have measured := actual_bit_index_tape_cost d row.length
  have tapeLen : L.result.length=row.length := measured.1
  have reads := map_sum_le_constant row (fun a=>16+4*(h+d+a.1.length))
    (16+4*(h+d+width)) (fun a ha=>by
      have H := hwidth a ha
      change 16+4*(h+d+a.1.length)≤16+4*(h+d+width)
      omega)
  constructor
  · change (row.zipWith _ L.result).length≤_
    rw [List.length_zipWith,tapeLen,min_self]
    exact hsize
  · change L.steps+5+(row.map (fun a=>16+4*(h+d+a.1.length))).sum≤_
    have lt : L.steps≤tapeFee d row.length := measured.2
    have step : L.steps+5+(row.map (fun a=>16+4*(h+d+a.1.length))).sum≤
        clauseParserRoof h d width row.length := by
      unfold clauseParserRoof
      omega
    refine step.trans ?_
    unfold clauseParserRoof tapeFee
    gcongr

theorem actual_row_parser_visits_no_more_than_its_input
    {h d : ℕ} (rows : BitsCNF) (labels : List (Word h)) (width size : ℕ)
    (rowFits : ∀ row∈rows,row.length≤size)
    (namesFit : ∀ row∈rows,∀ lit∈row,lit.1.length≤width) :
    let T := parseRows (d:=d) rows labels
    T.result.length≤rows.length ∧ T.result.flatten.length≤rows.length*size ∧
      T.steps≤2+rows.length*(clauseParserRoof h d width size+5) := by
  induction rows generalizing labels with
  | nil => simp [parseRows]
  | cons row rest ih =>
    cases labels with
    | nil => simp [parseRows]
    | cons k ks =>
      let A := parseClause (d:=d) k row
      let B := parseRows (d:=d) rest ks
      have localFee := leased_clause_fees_are_from_the_read_literal_bytes (d:=d) k row width size
        (rowFits row List.mem_cons_self) (namesFit row List.mem_cons_self)
      have restFee := ih ks (fun x hx=>rowFits x (List.mem_cons_of_mem _ hx))
        (fun x hx=>namesFit x (List.mem_cons_of_mem _ hx))
      change A.result.length≤size ∧ A.steps≤_ at localFee
      change B.result.length≤rest.length ∧ B.result.flatten.length≤_ ∧ B.steps≤_ at restFee
      change (A.result::B.result).length≤(row::rest).length ∧
        (A.result::B.result).flatten.length≤(row::rest).length*size ∧
        A.steps+B.steps+5≤2+(row::rest).length*(clauseParserRoof h d width size+5)
      simp only [List.length_cons,List.flatten_cons,List.length_append,Nat.add_mul,Nat.one_mul]
      omega

def guardParserRoof (h d width size rows : ℕ) : ℕ :=
  tapeFee h rows+2+rows*(clauseParserRoof h d width size+5)+5+4*(rows+rows*size)

theorem actual_guarded_parser_bit_time {h d : ℕ} (rows : BitsCNF) (width size : ℕ)
    (rowFits : ∀ row∈rows,row.length≤size)
    (namesFit : ∀ row∈rows,∀ lit∈row,lit.1.length≤width) :
    let P := parseGuard (h:=h) (d:=d) rows
    P.result.length≤rows.length*size ∧ P.steps≤guardParserRoof h d width size rows.length := by
  let K := indexTape h rows.length
  let R := parseRows (d:=d) rows K.result
  have B := actual_row_parser_visits_no_more_than_its_input (d:=d) rows K.result width size rowFits namesFit
  have fee : (indexTape h rows.length).steps≤tapeFee h rows.length := (actual_bit_index_tape_cost _ _).2
  change R.result.flatten.length≤rows.length*size ∧ K.steps+R.steps+5+4*(rows.length+R.result.flatten.length)≤_
  refine ⟨B.2.1,?_⟩
  unfold guardParserRoof
  dsimp only [K,R] at B ⊢
  omega

#print axioms leased_clause_fees_are_from_the_read_literal_bytes
#print axioms actual_row_parser_visits_no_more_than_its_input
#print axioms actual_guarded_parser_bit_time
end J6R109RawParserRate
