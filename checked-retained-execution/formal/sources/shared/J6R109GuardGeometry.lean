import J6R109RawParserRate

namespace J6R109RawParserRate
open AOracleMachineTime J6R49RootIngress
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false

theorem clean_never_adds_rows (F : BitsCNF) : (J7R9Clause.clean F).length≤F.length := by
  induction F with
  | nil => simp [J7R9Clause.clean]
  | cons c F ih =>
    cases m : J7R9Clause.taut c <;> simp [J7R9Clause.clean,m] <;> omega

theorem guarded_geometry_is_from_declared_input
    (declares : List (List Bool)) (F : BitsCNF) (w k : ℕ)
    (chart : ∀ name∈declares,name.length=w)
    (shape : ∀ row∈F,row.length≤k)
    (width : ∀ row∈F,∀ lit∈row,lit.1.length=w) :
    let V := (guardedMeter declares F).result
    V.length≤F.length+declares.length ∧
      (∀ row∈V,row.length≤k+2) ∧
      (∀ row∈V,∀ lit∈row,lit.1.length≤w+1) := by
  have ready : (guardedMeter declares F).result=
      (J7R9Clause.clean F).map (fun c=> ([false],false)::c.map tagLit)++
        declares.map (fun k=>[([false],true),(true::k,false)]) := by
    change (addGuards (safetyRows declares).result (cleanMeter F).result).result=_
    rw [clean_meter_exact,safety_rows_exact,add_guards_exact]
  dsimp only
  rw [ready]
  refine ⟨?_,?_,?_⟩
  · rw [List.length_append,List.length_map,List.length_map]
    exact Nat.add_le_add_right (clean_never_adds_rows F) _
  · intro row hr
    rcases List.mem_append.mp hr with H|H
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp H
      have r := J7R9Clause.clean_width k shape c hc
      simp only [List.length_cons,List.length_map]
      omega
    · obtain ⟨v,_,rfl⟩ := List.mem_map.mp H
      simp
  · intro row hr lit he
    rcases List.mem_append.mp hr with H|H
    · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp H
      rcases List.mem_cons.mp he with e|e
      · rw [e]; simp
      · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp e
        obtain ⟨old,hOld,_,rfl⟩ := J7R9Clause.clean_mem hc
        have z := width old hOld q (List.mem_dedup.mp hq)
        simp [tagLit,z]
    · obtain ⟨name,hName,rfl⟩ := List.mem_map.mp H
      simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with e|e
      · rw [e]; simp
      · rw [e]; simp [chart name hName]

#print axioms guarded_geometry_is_from_declared_input
end J6R109RawParserRate
