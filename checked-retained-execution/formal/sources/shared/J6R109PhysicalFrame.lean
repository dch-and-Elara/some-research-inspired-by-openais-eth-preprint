import J6R54PublicFamilyFresh

namespace J6R109PhysicalFrame
open AOracleMachineTime AOracleMachineTimeTape A1R10 J6R27PrescribedProbe
open J6R49RootIngress J6R51Ingress J6R50RootIngress J6R30GeneratedRootLayout J6R12CollisionEdges
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 11000000

theorem true_positive_writer_cost (e : ℕ) (one before : Word e) (n : ℕ) :
    (emitPositive e one before n).result.length=n ∧
      (emitPositive e one before n).steps=4+n*(20*e+6) := by
  induction n generalizing before with
  | zero => simp [emitPositive]
  | succ n ih =>
    have tail := ih (addWord before one).result
    have ad : (addWord before one).steps=12*e := by
      change (addBits before.val one.val).steps=12*e
      rw [(addBits_exact before.val one.val
         (before.property.trans one.property.symm)).2.2,before.property]
    constructor
    · change ((addWord before one).result::(emitPositive e one (addWord before one).result n).result).length=_
      rw [List.length_cons,tail.1]
    · change (addWord before one).steps+(emitPositive e one (addWord before one).result n).steps+
        8*e+6=4+(n+1)*(20*e+6)
      rw [ad,tail.2,Nat.add_mul,Nat.one_mul]
      omega

theorem actual_bit_index_tape_cost (w n : ℕ) :
    (indexTape w n).result.length=n ∧ (indexTape w n).steps≤tapeFee w n := by
  cases n with
  | zero => simp [indexTape,tapeFee]; omega
  | succ n =>
    let T := emitPositive w (wordOne w) (encoded w 0) n
    have h := true_positive_writer_cost w (wordOne w) (encoded w 0) n
    constructor
    · change (wordAt w 0::T.result).length=_
      rw [List.length_cons,show T.result.length=n from h.1]
    · change T.steps+3*w+6+3*w+4≤tapeFee w (n+1)
      rw [show T.steps=4+n*(20*w+6) from h.2]
      unfold tapeFee
      rw [Nat.add_mul,Nat.one_mul]
      omega

theorem zipper_left {U V : Type*} (xs : List U) (ys : List V) :
    ∀ p ∈ xs.zipWith Prod.mk ys, p.1 ∈ xs := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    cases ys with
    | nil => simp
    | cons y ys =>
      intro p hit
      simp only [List.zipWith_cons_cons,List.mem_cons] at hit ⊢
      rcases hit with h|h
      · exact Or.inl (congrArg Prod.fst h)
      · exact Or.inr (ih ys _ h)

theorem row_in_flatten_no_larger {A : Type*} (rows : List (List A))
    (row : List A) (hit : row∈rows) : row.length≤rows.flatten.length := by
  induction rows with
  | nil => simp at hit
  | cons xs ys ih =>
    simp only [List.mem_cons] at hit
    rcases hit with rfl|h
    · simp only [List.flatten_cons,List.length_append]
      omega
    · have hh := ih h
      simp only [List.flatten_cons,List.length_append]
      omega

def rowRankRoof (r c d wires wide len : ℕ) : ℕ :=
  tapeFee d len+
    (2+wires*(17+5*wide+12*c)+seedFee r c d+10*c+14+6)*len+
    7+len*(9+4*(r+c+d))

theorem one_actual_row_rank_cost {h d j r c : ℕ}
    (wires : List (WireKey h d j)) (row : Word r) (ports : List (PortSeed h d j))
    (wide : ℕ) (widths : ∀ u∈wires,keyWidth u≤wide) :
    (rankRow (c:=c) wires row ports).result.length≤ports.length ∧
      (rankRow (c:=c) wires row ports).steps≤rowRankRoof r c d wires.length wide ports.length := by
  let T := indexTape d ports.length
  let I := ports.zipWith (fun s k=>(s,k)) T.result
  let f := fun z : PortSeed h d j × Word d =>rankPort (c:=c) wires row z.2 z.1
  let Z := mapMeter f I
  have idx := actual_bit_index_tape_cost d ports.length
  have len : I.length=ports.length := by
    change (ports.zipWith _ T.result).length=_
    rw [List.length_zipWith, show T.result.length=ports.length from idx.1,min_self]
  have rows := mapMeter_exact f (fun x=>(f x).result)
    (2+wires.length*(17+5*wide+12*c)+seedFee r c d+10*c+14) I
    (fun z _=>⟨rfl,port_rank_fee wires row z.2 z.1 wide widths⟩)
  have lim : (Z.result.filterMap id).length≤I.length := by
    change (Z.result.filterMap id).length≤_
    rw [show Z.result=_ from rows.1, List.filterMap_map]
    simpa only using List.length_filterMap_le (f:=id ∘ (fun x=>(f x).result)) (l:=I)
  constructor
  · change (Z.result.filterMap id).length≤_
    exact lim.trans_eq len
  · change T.steps+Z.steps+7+I.length*(9+4*(r+c+d))≤_
    have Tpaid : T.steps≤tapeFee d ports.length := idx.2
    have Zpaid : Z.steps≤_ := rows.2
    unfold rowRankRoof
    rw [len] at Zpaid ⊢
    omega

#print axioms true_positive_writer_cost
#print axioms actual_bit_index_tape_cost
#print axioms one_actual_row_rank_cost
end J6R109PhysicalFrame
