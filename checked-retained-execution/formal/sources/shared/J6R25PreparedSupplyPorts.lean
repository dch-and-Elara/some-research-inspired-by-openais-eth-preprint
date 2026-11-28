import J6R21AncestorRegistry

/-! Charged sequential filtering of an installed parent half-port file.
Both endpoints of a parent edge are independent records. The scan
consumes payload bytes even on discarded rows, so skipping a row
does not assume free jumping over a variable-length record. -/
namespace J6R25PreparedSupply
open AOracleMachineTime J6R15ModeCost J6R21Ancestor

structure PortRow (w : ℕ) where
  address : Word w
  group : Word 6
  body : List Bool

def rowScanFee {w : ℕ} (row : PortRow w) : ℕ := 2*w+3*row.body.length+81

def selectPorts {w : ℕ} (key : Word 6) : List (PortRow w)→Meter (List (PortRow w))
  | [] => ⟨[],3⟩
  | row::rest =>
    let read := copyBytes row.body
    let hit := cmpAddr key row.group
    let out := selectPorts key rest
    let answer := if hit.result then { row with body := read.result }::out.result else out.result
    ⟨answer,out.steps+read.steps+hit.steps+2*w+15⟩

theorem select_ports_exact {w : ℕ} (key : Word 6) (rows : List (PortRow w)) :
    let z := selectPorts key rows
    z.result=(rows.filter (fun row=>(cmpAddr key row.group).result)) ∧
    z.steps=3+(rows.map rowScanFee).sum := by
  dsimp only
  induction rows with
  | nil => exact ⟨rfl,rfl⟩
  | cons row rows ih =>
    have cmp := (cmpAddr_exact key row.group).2
    have pay := copyBytes_exact row.body
    constructor
    · change (if (cmpAddr key row.group).result then
          { row with body := (copyBytes row.body).result }::(selectPorts key rows).result
        else (selectPorts key rows).result)=_
      rw [pay,ih.1]
      cases row with
      | mk addr grp body =>
        cases h : (cmpAddr key grp).result <;>
          simp only [List.filter_cons,h,Bool.false_eq_true,if_false,if_true]
    · change (selectPorts key rows).steps+(copyBytes row.body).steps+(cmpAddr key row.group).steps+2*w+15=_
      rw [cmp,pay,ih.2]
      simp only [List.map_cons,List.sum_cons,rowScanFee]
      omega

def countList {A : Type*} (width : ℕ) : List A→Meter (Word width)
  | [] => ⟨word 0,width+3⟩
  | _::xs =>
    let x := countList width xs
    let y := increment x.result
    ⟨y.result,x.steps+y.steps+4⟩

theorem count_list_exact {A : Type*} {w : ℕ} (hw : 0<w) (xs : List A) (fit : xs.length<2^w) :
    (countList w xs).result.val=xs.length ∧
    (countList w xs).steps=w+3+xs.length*(13*w+8) := by
  induction xs with
  | nil => exact ⟨word_val (by positivity),by simp only [countList,List.length_nil,Nat.zero_mul,Nat.add_zero]⟩
  | cons x xs ih =>
    have hFit : xs.length<2^w := Nat.lt_trans (Nat.lt_succ_self _) fit
    obtain ⟨ev,et⟩ := ih hFit
    obtain ⟨hv,ht⟩ := increment_exact hw (countList w xs).result (by simpa only [ev,List.length_cons] using fit)
    constructor
    · change (increment (countList w xs).result).result.val=xs.length+1
      rw [hv,ev]
    · change (countList w xs).steps+(increment (countList w xs).result).steps+4=_
      simp only [et,ht,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega

def childPortsWithCount {w b : ℕ} (key : Word 6) (rows : List (PortRow w)) :
    Meter (List (PortRow w)×Word b) :=
  let P := selectPorts key rows
  let C := countList b P.result
  ⟨(P.result,C.result),P.steps+C.steps+4⟩

theorem ports_counted {w b : ℕ} (hb : 0<b) (key : Word 6) (rows : List (PortRow w))
    (fit : (rows.filter (fun row=>(cmpAddr key row.group).result)).length<2^b) :
    let R := childPortsWithCount (b:=b) key rows
    R.result.1=(rows.filter (fun row=>(cmpAddr key row.group).result)) ∧
    R.result.2.val=R.result.1.length ∧
    R.steps=3+(rows.map rowScanFee).sum+(b+3+R.result.1.length*(13*b+8))+4 := by
  let P := selectPorts key rows
  have hP := select_ports_exact key rows
  have hC := count_list_exact hb P.result (by rwa [hP.1])
  exact ⟨hP.1,hC.1,by
    change P.steps+(countList b P.result).steps+4=_
    rw [show P.steps=3+(rows.map rowScanFee).sum from hP.2,hC.2]
    rfl⟩

#print axioms select_ports_exact
#print axioms count_list_exact
#print axioms ports_counted
end J6R25PreparedSupply

