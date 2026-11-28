import J6R49DFSProbe

/-! Proof-side dynamic cuts of the actual halt-driven run. The current
mode accumulator and the current group accumulator are values of
their true prefixes. No trace list is constructed by the evaluator. -/
namespace J6R49DFS
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J6R25PreparedSupply J6R48DFS
open J6R15ModeCost (State Pulse Runs strictTuples_exact Word.val)

set_option autoImplicit false
set_option maxRecDepth 2300
set_option maxHeartbeats 5400000

variable {q n : ℕ} {A : Type*}
local notation "W" => J6R15ModeCost.Word q

inductive ModePrefix (op : A→List W→Meter A) (initial : Pending q n) (a₀ : A) (fee₀ : ℕ) :
    Pending q n→A→ℕ→Prop where
  | begin : ModePrefix op initial a₀ fee₀ initial a₀ fee₀
  | after {cur : Pending q n} {acc : A} {fee : ℕ} {raw : List W} {st : State q} :
      ModePrefix op initial a₀ fee₀ cur acc fee→
      (e : cur.pulse.result=.emit raw st)→
      ModePrefix op initial a₀ fee₀ (cur.tail e) (op acc raw).result
        (fee+cur.pulse.steps+(op acc raw).steps)

theorem drain_next_is_real (op : A→List W→Meter A) (cur : Pending q n) (acc : A) (fee : ℕ)
    {raw : List W} {st : State q} (e : cur.pulse.result=.emit raw st) :
    modeDrain op cur acc fee=
      modeDrain op (cur.tail e) (op acc raw).result (fee+cur.pulse.steps+(op acc raw).steps) := by
  rw [modeDrain]
  dsimp only
  split
  · rename_i _ h
    rw [e] at h
    cases h
  · rename_i h
    rw [e] at h
    cases h
  · rename_i em next actual
    have ev := actual.symm.trans e
    cases ev
    rfl

theorem mode_prefix_continuation (op : A→List W→Meter A) (initial : Pending q n)
    (a₀ : A) (fee₀ : ℕ) {cur : Pending q n} {acc : A} {fee : ℕ}
    (p : ModePrefix op initial a₀ fee₀ cur acc fee) :
    modeDrain op initial a₀ fee₀=modeDrain op cur acc fee := by
  induction p with
  | begin => rfl
  | after _ e ih => exact ih.trans (drain_next_is_real _ _ _ _ e)

theorem mode_prefix_keeps_actual_suffix (op : A→List W→Meter A) (initial : Pending q n)
    (a₀ : A) (fee₀ : ℕ) (X : List (List ℕ)) (trace : Runs n initial.state X (.ascend []))
    {cur : Pending q n} {acc : A} {fee : ℕ} (pref : ModePrefix op initial a₀ fee₀ cur acc fee) :
    ∃ done rem, X=done++rem ∧ Runs n cur.state rem (.ascend []) := by
  induction pref with
  | begin => exact ⟨[],X,rfl,trace⟩
  | @after cur acc fee raw st _ emitted ih =>
    obtain ⟨done,rem,val,tr⟩ := ih
    obtain ⟨rest,rfl,_,hRun⟩ := cur.next_data emitted tr
    exact ⟨done++[raw.map J6R15ModeCost.Word.val],rest,by simpa only
      [List.append_assoc,List.singleton_append] using val,hRun⟩

theorem actual_emission_mem_run (op : A→List W→Meter A) (initial : Pending q n)
    (a₀ : A) (fee₀ : ℕ) (X : List (List ℕ)) (trace : Runs n initial.state X (.ascend []))
    {cur : Pending q n} {acc : A} {fee : ℕ} (pref : ModePrefix op initial a₀ fee₀ cur acc fee)
    {raw : List W} {st : State q} (em : cur.pulse.result=.emit raw st) :
    raw.map J6R15ModeCost.Word.val∈X := by
  obtain ⟨done,rem,e,tr⟩ := mode_prefix_keeps_actual_suffix op initial a₀ fee₀ X trace pref
  obtain ⟨rest,rfl,_,_⟩ := cur.next_data em tr
  rw [e]
  exact List.mem_append_right _ List.mem_cons_self

section Product

inductive LeftPrefix {A B : Type*} (op : A→B→Meter A) (xs : List B) (a₀ : A) (fee₀ : ℕ) :
    List B→A→ℕ→Prop where
  | begin : LeftPrefix op xs a₀ fee₀ xs a₀ fee₀
  | after {g : B} {gs : List B} {u : A} {fee : ℕ} :
      LeftPrefix op xs a₀ fee₀ (g::gs) u fee→
      LeftPrefix op xs a₀ fee₀ gs (op u g).result (fee+(op u g).steps)

abbrev GroupPrefix {p ell : ℕ} {fw : List (A1R10.Word p)} (hp : 0<p)
    (read : Fin 64→Meter (UVBlock fw ell)) (u₀ : UVBlock fw ell) (fee₀ : ℕ) :
    List (Fin 64)→UVBlock fw ell→ℕ→Prop :=
  LeftPrefix (fun u g=>mulM hp ⟨u,0⟩ (read g)) (groupOrder 64) u₀ fee₀

theorem group_prefix_continuation {p ell : ℕ} {fw : List (A1R10.Word p)} (hp : 0<p)
    (read : Fin 64→Meter (UVBlock fw ell)) (u₀ : UVBlock fw ell) (fee₀ : ℕ)
    {more : List (Fin 64)} {u : UVBlock fw ell} {fee : ℕ}
    (pref : GroupPrefix hp read u₀ fee₀ more u fee) :
    productCursor hp read (groupOrder 64) u₀ fee₀=productCursor hp read more u fee := by
  induction pref with
  | begin => rfl
  | after _ ih => exact ih.trans rfl

theorem real_group_invocation {p ell : ℕ} {fw : List (A1R10.Word p)} (hp : 0<p)
    (read : Fin 64→Meter (UVBlock fw ell)) (u₀ : UVBlock fw ell) (fee₀ : ℕ)
    {g : Fin 64} {more : List (Fin 64)} {u : UVBlock fw ell} {fee : ℕ}
    (pref : GroupPrefix hp read u₀ fee₀ (g::more) u fee) :
    productCursor hp read (groupOrder 64) u₀ fee₀=
      productCursor hp read more (mulM hp ⟨u,0⟩ (read g)).result (fee+(mulM hp ⟨u,0⟩ (read g)).steps) :=
  (group_prefix_continuation hp read u₀ fee₀ pref).trans rfl
end Product

#print axioms drain_next_is_real
#print axioms mode_prefix_continuation
#print axioms mode_prefix_keeps_actual_suffix
#print axioms actual_emission_mem_run
#print axioms group_prefix_continuation
#print axioms real_group_invocation
end J6R49DFS
