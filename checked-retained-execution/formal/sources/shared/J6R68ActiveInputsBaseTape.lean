import J6R68ActiveInputsBaseOrder

/-! One literal current-node pass builds the signed, positive-order
retained roster. Production does not use the previous ActiveMachine
list as input or enumerate any beta vectors. -/
namespace J6R68ActiveInputs
open AOracleMachineTime AOracleMachineTimeTape A1R10 J6R22RootReadout
open J6R12CollisionMenu J6ActiveSchedule J6R52FreshExterior

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13500000
set_option maxRecDepth 3200
set_option Elab.async false

def scanOrders {q : ℕ} (zero h : Word q) (axis taper : List Bool) :
    List (List Bool) → Meter (List (RawCentre q))
  | []=>⟨[],2⟩
  | bits::xs=>
    let row := readOrder zero h axis taper bits
    let tail := scanOrders zero h axis taper xs
    ⟨row.result.toList++tail.result,row.steps+tail.steps+5⟩

theorem actual_orders_are_stable {q : ℕ}
    (zero h : Word q) (axis taper : List Bool) (keys : List (List Bool))
    (keyExact : ∀ x∈keys,∀ r∈(readOrder zero h axis taper x).result,r.key=x)
    (localCap : ℕ) (fee : ∀ x∈keys,(readOrder zero h axis taper x).steps ≤ localCap) :
    let out := scanOrders zero h axis taper keys
    out.result=keys.filterMap (fun x=>(readOrder zero h axis taper x).result) ∧
    out.result.map RawCentre.key=keys.filter (fun x=>(readOrder zero h axis taper x).result.isSome) ∧
    out.steps ≤ (localCap+5)*keys.length+2 := by
  induction keys with
  | nil => simp [scanOrders]
  | cons k ks ih =>
    let row := readOrder zero h axis taper k
    have H := ih (fun x z=>keyExact x (List.mem_cons_of_mem _ z))
      (fun x z=>fee x (List.mem_cons_of_mem _ z))
    have f : row.steps ≤ localCap := fee k List.mem_cons_self
    constructor
    · dsimp only [scanOrders]
      rw [H.1]
      change row.result.toList++List.filterMap (fun x=>(readOrder zero h axis taper x).result) ks=_
      cases m : row.result with
      | none =>
        have m' : (readOrder zero h axis taper k).result=none := m
        simp [m']
      | some val =>
        have m' : (readOrder zero h axis taper k).result=some val := m
        simp [m']
    · constructor
      · dsimp only [scanOrders]
        rw [List.map_append,H.2.1]
        change (row.result.toList.map RawCentre.key)++_ = _
        cases m : row.result with
        | none =>
          have m' : (readOrder zero h axis taper k).result=none := m
          simp [m']
        | some r =>
          have m' : (readOrder zero h axis taper k).result=some r := m
          have Eq : r.key=k := keyExact k List.mem_cons_self r (by change r∈row.result; rw [m]; simp)
          simp [m',Eq]
      · change row.steps+(scanOrders zero h axis taper ks).steps+5 ≤ (localCap+5)*(ks.length+1)+2
        rw [Nat.mul_succ]
        have feeT := H.2.2
        omega

def rosterRowBound (a u q : ℕ) : ℕ :=
  10*(a+1)+11+(4*a+3)+(2+(wordArithmeticRoof q+5)*u)+10*q+7

def paidBaseTape {q : ℕ} (hq : 0<q) (a u : ℕ) (edge taper : J6R15ModeCost.Word q) :
    Meter (List (RawCentre q)) :=
  let A := ticks a
  let U := ticks u
  let G := signedGridTape a
  let H := heightWord hq edge taper
  let z := constantRegister q []
  let d := scanOrders z.result H.result A.result U.result G.result
  ⟨d.result,A.steps+U.steps+G.steps+H.steps+z.steps+d.steps+8⟩

def baseTapeRoof (a u q : ℕ) : ℕ :=
  (4*a+2)+(4*u+2)+16*(a+2)*2^(a+1)+heightWordRoof q+(4*q+4)+
    ((rosterRowBound a u q+5)*2^(a+1)+2)+8

def centreRowValue {q : ℕ} (a : ℕ) (r : RawCentre q) : ℤ×ℕ :=
  (offsetCentre a r.key,bitsValue r.multiplicity.val)

theorem actual_base_tape_has_stock_census {q a M u : ℕ} (hq : 0<q) (edge taper : J6R15ModeCost.Word q)
    (e : edge.val=M) (v : taper.val=u) (hu : 0<u) (hm : u ≤ M)
    (num : 3*M+u-1<2^q) (fit : 4*M<2^q) :
    let B := paidBaseTape hq a u edge taper
    let ys := B.result.map (centreRowValue a)
    (ys.map Prod.fst).Nodup ∧ (ys.map Prod.fst).toFinset=active a M u ∧
    (∀ r∈B.result,r.key.length=a+1 ∧ (centreRowValue a r).2=order M u (centreRowValue a r).1) ∧
    B.steps ≤ baseTapeRoof a u q := by
  let A := ticks a
  let U := ticks u
  let G := signedGridTape a
  let H := heightWord hq edge taper
  let z := constantRegister q []
  let d := scanOrders z.result H.result A.result U.result G.result
  have gh := paid_grid_exact a
  have hX : bitsValue H.result.val=height M u := by
    have exactValue := actual_height_word_exact hq edge taper (v.symm ▸ hu) (e.symm ▸ v.symm ▸ num)
    rwa [e,v] at exactValue
  have hz : bitsValue z.result.val=0 := by
    apply exact_nat_of_register_read z.result (by positivity)
    simp [z,constant_register_read,bitsValue]
  have law (bits : List Bool) (mem : bits∈G.result) :=
    read_order_is_stock hq z.result H.result hz hX A.result U.result bits (ticks_exact a).1
      (ticks_exact u).1 ((binary_mem _ _).1 (gh.1 ▸ mem)) hu hm fit
  obtain ⟨sameRows,sameKeys,fee⟩ := actual_orders_are_stable z.result H.result A.result U.result G.result
    (fun w h r m=>((law w h).2.1 r m).1) (rosterRowBound a u q) (fun w mem=>(law w mem).2.2)
  have eqProj : ((d.result.map (centreRowValue a)).map Prod.fst) =
      (G.result.filter (fun x=>(readOrder z.result H.result A.result U.result x).result.isSome)).map
        (offsetCentre a) := by
    change (d.result.map (centreRowValue a)).map Prod.fst=_
    rw [←show d.result.map RawCentre.key=_ from sameKeys,List.map_map,List.map_map]
    rfl
  change ((d.result.map (centreRowValue a)).map Prod.fst).Nodup ∧
    ((d.result.map (centreRowValue a)).map Prod.fst).toFinset=active a M u ∧ _
  refine ⟨?_,?_,?_,?_⟩
  · rw [eqProj]
    exact ((List.filter_sublist (p:=fun x=>(readOrder z.result H.result A.result U.result x).result.isSome)
      (l:=G.result)).map (offsetCentre a)).nodup gh.2.1
  · rw [eqProj]
    ext t
    simp only [List.mem_toFinset,List.mem_map,List.mem_filter]
    constructor
    · rintro ⟨bits,⟨mem,yes⟩,rfl⟩
      exact (law bits mem).1.mp yes
    · intro ha
      obtain ⟨bits,len,val⟩ := printed_grid_has_exact_word a t ((J6R9Recursive.active_grid a M u ha).1)
      have mem : bits∈G.result := gh.1.symm ▸ (binary_mem _ _).2 len
      exact ⟨bits,⟨mem,(law bits mem).1.mpr (val.symm ▸ ha)⟩,val⟩
  · intro r mem
    have ins : r∈G.result.filterMap (fun x=>(readOrder z.result H.result A.result U.result x).result) :=
      sameRows ▸ mem
    obtain ⟨bits,belongs,which⟩ := List.mem_filterMap.mp ins
    have values := (law bits belongs).2.1 r (by rw [which]; simp)
    exact ⟨values.1.symm ▸ (binary_mem _ _).1 (gh.1 ▸ belongs),by
      change bitsValue r.multiplicity.val=order M u (offsetCentre a r.key)
      rw [values.1]
      exact values.2⟩
  · change A.steps+U.steps+G.steps+H.steps+z.steps+d.steps+8 ≤ _
    have boundG := gh.2.2.2
    have gl : G.result.length=2^(a+1) := (congrArg List.length gh.1).trans (binary_length (a+1))
    have boundD : d.steps ≤ (rosterRowBound a u q+5)*2^(a+1)+2 := by rwa [gl] at fee
    have boundH := actual_height_word_fee hq edge taper
    have ZA := (ticks_exact a).2
    have ZU := (ticks_exact u).2
    have zz := constant_register_fee q []
    unfold baseTapeRoof
    change G.steps ≤ _ at boundG
    change H.steps ≤ _ at boundH
    change A.steps = _ at ZA
    change U.steps = _ at ZU
    change z.steps = _ at zz
    omega

#print axioms actual_orders_are_stable
#print axioms actual_base_tape_has_stock_census
end J6R68ActiveInputs
