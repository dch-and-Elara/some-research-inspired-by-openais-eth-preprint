import J6R53OldOwnerTape

/-! A raw origin lookup tape is produced from the returned owner roster,
not guessed from physical half-ports. Preserve every owner, including an
isolated Gate or Page. The new two-word row copies the name twice and
copies its actual origin; no Gate expression needs to be reconstructed. -/
namespace J6R55TerminalOrigin
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor J6R36ChildFramedRoute J6R53OldOwner J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

abbrev OriginRows (own key prec page : ℕ) := List (RefRow own (Word own × Origin key prec page))

def originRow {own gate key prec page : ℕ}
    (u : RefRow own (OwnerData gate key prec page)) : RefRow own (Word own × Origin key prec page) :=
  ⟨u.address,(u.address,u.payload.origin)⟩

def projectOriginTape {own gate key prec page : ℕ} :
    RawRoster own gate key prec page→Meter (OriginRows own key prec page)
  | []=>⟨[],3⟩
  | a::as=>
    let addr := copyFixed a.address
    let owner := copyFixed a.address
    let tag := copyOrigin a.payload.origin
    let tail := projectOriginTape as
    ⟨⟨addr.result,(owner.result,tag.result)⟩::tail.result,
      addr.steps+owner.steps+tag.steps+tail.steps+6⟩

theorem project_origin_tape_exact {own gate key prec page : ℕ}
    (rows : RawRoster own gate key prec page) :
    projectOriginTape rows=⟨rows.map originRow,3+(rows.map (fun u=>2*(3*own+1)+
      originFee key prec page u.payload.origin.pageKey.isSome+6)).sum⟩ := by
  induction rows with
  | nil=>rfl
  | cons a as ih=>
    simp only [projectOriginTape,originRow,copy_fixed_exact,copy_origin_exact,ih,List.map_cons,List.sum_cons]
    congr 1
    omega

variable {V : Type} {own gate key prec page : ℕ}
variable {name : V→Word own} {values : V→OwnerData gate key prec page}
variable (R : CompleteRoster name values)
variable {tags : V→Origin key prec page}
variable (tagLaw : ∀ x,(values x).origin=tags x)

include tagLaw in
theorem project_roster_exact (x : V) :
    (⟨name x,(name x,tags x)⟩ : RefRow own _)∈(projectOriginTape R.raw).result := by
  rw [project_origin_tape_exact]
  rw [R.exactRows]
  refine List.mem_map.mpr ⟨⟨name x,values x⟩,List.mem_map.mpr ⟨x,R.complete x,rfl⟩,?_⟩
  simp only [originRow,tagLaw x]

include tagLaw in
theorem project_roster_unique (inj : Function.Injective name) (x : V)
    (row : RefRow own (Word own × Origin key prec page))
    (found : row∈(projectOriginTape R.raw).result) (same : row.address=name x) :
    row.payload=(name x,tags x) := by
  rw [project_origin_tape_exact] at found
  rw [R.exactRows] at found
  obtain ⟨raw,old,rfl⟩ := List.mem_map.mp found
  obtain ⟨y,_,rfl⟩ := List.mem_map.mp old
  have h : y=x := inj same
  subst y
  simp only [originRow,tagLaw x]

end
#print axioms project_origin_tape_exact
#print axioms project_roster_exact
#print axioms project_roster_unique
end J6R55TerminalOrigin
