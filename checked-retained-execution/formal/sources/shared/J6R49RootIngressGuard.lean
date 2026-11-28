import J6R49RootIngressClean
import J7R9SourceInput

/-! A faithful, metered raw syntax producer for the *same* guarded CNF.
The source variable-declaration list comes from the input, not from
the set of occurrences that happen to survive clause cleanup. -/
namespace J6R49RootIngress
open Std.Sat AOracleMachineTime J6R21Ancestor
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6000000

def codeLit {V : Type*} (code : V→List Bool) (p : V×Bool) : BitsLit := (code p.1,p.2)
def codeCNF {V : Type*} (code : V→List Bool) (F : CNF V) : BitsCNF :=
  F.map (List.map (codeLit code))

theorem code_lit_injective {V : Type*} (code : V→List Bool) (inj : Function.Injective code) :
    Function.Injective (codeLit code) := by
  intro a b h
  exact Prod.ext (inj (congrArg (fun a : BitsLit => a.1) h)) (congrArg (fun a : BitsLit => a.2) h)

theorem coded_taut {V : Type*} [DecidableEq V] (code : V→List Bool)
    (inj : Function.Injective code) (c : CNF.Clause V) :
    J7R9Clause.taut (c.map (codeLit code)) = J7R9Clause.taut c := by
  apply Bool.eq_iff_iff.mpr
  rw [J7R9Clause.taut_true,J7R9Clause.taut_true]
  constructor
  · rintro ⟨x,hx,hy⟩
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hy
    have he' : codeLit code b = codeLit code (a.1,!a.2) := he
    exact ⟨a,ha,code_lit_injective code inj he' ▸ hb⟩
  · rintro ⟨a,ha,hb⟩
    exact ⟨codeLit code a,List.mem_map_of_mem ha,List.mem_map_of_mem hb⟩

theorem same_clean_code {V : Type*} [DecidableEq V] (code : V→List Bool)
    (inj : Function.Injective code) (F : CNF V) :
    J7R9Clause.clean (codeCNF code F) = codeCNF code (J7R9Clause.clean F) := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    have ht := coded_taut code inj c
    unfold codeCNF at ih
    cases h : J7R9Clause.taut c <;>
      simp [codeCNF,J7R9Clause.clean,ht,h,ih,
        List.dedup_map_of_injective (code_lit_injective code inj)]

def guardCode {V : Type*} (code : V→List Bool) : Option V→List Bool
  | none => [false]
  | some v => true::code v

theorem guard_code_injective {V : Type*} (code : V→List Bool) (inj : Function.Injective code) :
    Function.Injective (guardCode code) := by
  intro a b h
  rcases a with _|v <;> rcases b with _|w <;> simp [guardCode] at h ⊢
  exact inj h

def tagLit (p : BitsLit) : BitsLit := (true::p.1,p.2)

def tagRows : BitsClause→Meter BitsClause
  | [] => ⟨[],1⟩
  | p::ps =>
    let a := copyBytes p.1
    let b := tagRows ps
    ⟨(true::a.result,p.2)::b.result,a.steps+b.steps+5⟩

theorem tag_rows_exact (ps : BitsClause) :
    (tagRows ps).result=ps.map tagLit := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [tagRows,copyBytes_exact,ih,tagLit]

theorem tag_rows_steps (ps : BitsClause) (w : ℕ) (h : ∀ p∈ps,p.1.length=w) :
    (tagRows ps).steps≤1+ps.length*(3*w+6) := by
  induction ps with
  | nil => simp [tagRows]
  | cons p ps ih =>
    have a := congrArg Meter.steps (copyBytes_exact p.1)
    change (copyBytes p.1).steps=3*p.1.length+1 at a
    rw [h p List.mem_cons_self] at a
    have b := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [tagRows,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

def safetyRows : List (List Bool)→Meter BitsCNF
  | [] => ⟨[],1⟩
  | k::ks =>
    let a := copyBytes k
    let b := safetyRows ks
    ⟨[([false],true),(true::a.result,false)]::b.result,a.steps+b.steps+9⟩

theorem safety_rows_exact (ks : List (List Bool)) :
    (safetyRows ks).result=ks.map (fun k => [([false],true),(true::k,false)]) := by
  induction ks with
  | nil => rfl
  | cons k ks ih => simp [safetyRows,copyBytes_exact,ih]

theorem safety_rows_steps (ks : List (List Bool)) (w : ℕ) (h : ∀ k∈ks,k.length=w) :
    (safetyRows ks).steps≤1+ks.length*(3*w+10) := by
  induction ks with
  | nil => simp [safetyRows]
  | cons k ks ih =>
    have a := congrArg Meter.steps (copyBytes_exact k)
    change (copyBytes k).steps=3*k.length+1 at a
    rw [h k List.mem_cons_self] at a
    have b := ih (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [safetyRows,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

def addGuards (tail : BitsCNF) : BitsCNF→Meter BitsCNF
  | [] => ⟨tail,1⟩
  | c::cs =>
    let a := tagRows c
    let b := addGuards tail cs
    ⟨(([false],false)::a.result)::b.result,a.steps+b.steps+6⟩

theorem add_guards_exact (tail F : BitsCNF) :
    (addGuards tail F).result=F.map (fun c => ([false],false)::c.map tagLit)++tail := by
  induction F with
  | nil => rfl
  | cons c F ih => simp [addGuards,tag_rows_exact,ih]

theorem add_guards_steps (tail F : BitsCNF) (w k : ℕ)
    (size : ∀ c∈F,c.length≤k) (width : ∀ c∈F,∀ p∈c,p.1.length=w) :
    (addGuards tail F).steps≤1+F.length*(7+k*(3*w+6)) := by
  induction F with
  | nil => simp [addGuards]
  | cons c F ih =>
    have hf := size c List.mem_cons_self
    have a := (tag_rows_steps c w (width c List.mem_cons_self)).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hf) 1)
    have b := ih (fun z hz => size z (List.mem_cons_of_mem _ hz))
      (fun z hz => width z (List.mem_cons_of_mem _ hz))
    simp only [addGuards,List.length_cons]
    rw [Nat.add_mul,Nat.one_mul]
    omega

def guardedMeter (declarations : List (List Bool)) (raw : BitsCNF) : Meter BitsCNF :=
  let a := cleanMeter raw
  let b := safetyRows declarations
  let c := addGuards b.result a.result
  ⟨c.result,a.steps+b.steps+c.steps+6⟩

theorem paid_guard_original_syntax {V : Type*} [Fintype V] [DecidableEq V]
    (code : V→List Bool) (inj : Function.Injective code) (F : CNF V) :
    (guardedMeter ((Finset.univ : Finset V).toList.map code) (codeCNF code F)).result =
      codeCNF (guardCode code) (J7R9SourceInput.H F) := by
  change (addGuards (safetyRows ((Finset.univ : Finset V).toList.map code)).result
      (cleanMeter (codeCNF code F)).result).result=_
  rw [add_guards_exact,safety_rows_exact,clean_meter_exact,same_clean_code code inj]
  simp [codeCNF,J7R9SourceInput.H,J6Guard.guardedFormula,List.map_map,List.map_append,
    Function.comp_def,guardCode,tagLit,codeLit,J6Guard.mapLit]

def fullIngressFee (w k rows vars : ℕ) : ℕ :=
  9+rows*(cleanFee w k+(7+k*(3*w+6)))+vars*(3*w+10)

private theorem clean_list_length (F : BitsCNF) :
    (J7R9Clause.clean F).length ≤ F.length := by
  induction F with
  | nil => simp [J7R9Clause.clean]
  | cons c F ih => cases h : J7R9Clause.taut c <;> simp [J7R9Clause.clean,h] <;> omega

theorem paid_guard_source_cost (declares : List (List Bool)) (F : BitsCNF) (w k : ℕ)
    (chart : ∀ a∈declares,a.length=w)
    (size : ∀ c∈F,c.length≤k) (width : ∀ c∈F,∀ a∈c,a.1.length=w) :
    (guardedMeter declares F).steps≤fullIngressFee w k F.length declares.length := by
  let A := cleanMeter F
  let S := (safetyRows declares).result
  have a := clean_meter_steps F w k size width
  change A.steps≤1+F.length*cleanFee w k at a
  have b := safety_rows_steps declares w chart
  have sub : A.result.length≤F.length := by
    rw [show A.result=J7R9Clause.clean F from clean_meter_exact F]
    exact clean_list_length F
  have hs : ∀ c∈A.result,c.length≤k := by
    rw [show A.result=J7R9Clause.clean F from clean_meter_exact F]
    exact J7R9Clause.clean_width k size
  have hw : ∀ c∈A.result,∀ a∈c,a.1.length=w := by
    rw [show A.result=J7R9Clause.clean F from clean_meter_exact F]
    intro c hc a ha
    obtain ⟨d,hd,_,rfl⟩ := J7R9Clause.clean_mem hc
    exact width d hd a (List.mem_dedup.mp ha)
  have c := (add_guards_steps S A.result w k hs hw).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ sub) 1)
  change A.steps+(safetyRows declares).steps+(addGuards S A.result).steps+6≤_
  unfold fullIngressFee
  rw [Nat.mul_add]
  omega

#print axioms code_lit_injective
#print axioms coded_taut
#print axioms same_clean_code
#print axioms guard_code_injective
#print axioms paid_guard_original_syntax
#print axioms paid_guard_source_cost
end J6R49RootIngress
