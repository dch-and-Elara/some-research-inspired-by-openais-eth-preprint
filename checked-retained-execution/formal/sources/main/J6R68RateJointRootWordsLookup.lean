import J6R58BootScopeReads

/-! Complete lookup answers alone do not justify replacing the scan
length by a graph census. This is an operation-level regression on
the same paid original boot reference reader. -/
namespace J6R68RateJoint.RootWords
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate J6R58BootScope
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2900
set_option maxHeartbeats 7000000
set_option Elab.async false

theorem irrelevant_prefix_exact_scan {D : Type*} {w : ℕ} (key : Word w) (row : RefRow w D)
    (neq : key≠row.address) (rows : List (RefRow w D)) (n : ℕ) :
    locate key (List.replicate n row++rows)=
      ⟨(locate key rows).result,n*(13*w+13)+(locate key rows).steps⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have q := cmpAddr_exact key row.address
    have miss : (cmpAddr key row.address).result=false :=
      Bool.eq_false_iff.mpr (fun x=>neq (q.1.mp x))
    rw [List.replicate_succ,List.cons_append,locate,if_neg (fun yes=>Bool.false_ne_true (miss.symm.trans yes))]
    change (⟨(locate key (List.replicate n row++rows)).result,
      ((cmpAddr key row.address).steps+3*w+8)+(locate key (List.replicate n row++rows)).steps⟩ :
        Meter (Option D))=_
    rw [ih,q.2]
    apply congrArg (fun fees => (⟨(locate key rows).result,fees⟩ : Meter (Option D)))
    change ((10*w+5)+3*w+8)+(n*(13*w+13)+(locate key rows).steps)=
      (n+1)*(13*w+13)+(locate key rows).steps
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem actual_boot_handle_fee_cannot_be_capped_by_correct_hit
    {D : Type*} {w : ℕ} (key : Word w) (row : RefRow w D)
    (neq : key≠row.address) (rows : List (RefRow w D))
    (obj : D) (hit : (locate key rows).result=some obj) (added : ℕ) :
    let old := readBootReference rows key
    let new := readBootReference (List.replicate added row++rows) key
    old.result=new.result ∧ new.result=some obj ∧
      new.steps=old.steps+added*(13*w+13) := by
  have h := irrelevant_prefix_exact_scan key row neq rows added
  dsimp only
  unfold readBootReference
  simp only [copy_fixed_exact,h,hit]
  exact ⟨True.intro,True.intro,by omega⟩

#print axioms irrelevant_prefix_exact_scan
#print axioms actual_boot_handle_fee_cannot_be_capped_by_correct_hit
end J6R68RateJoint.RootWords

