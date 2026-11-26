import P5AlwaysSatOriginalPhysicalPorts

/-! Each factor fibre is exactly its original ordered literal list,
with no cardinality loss by treating a clause as a distinct-variable scope. -/
namespace Paper5.AlwaysSatOriginal.Physical
open scoped BigOperators Classical
variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

theorem port_list_nodup (f : CloneFactor E T) : (portList E T f).Nodup := by
  rcases f with f|p
  · apply List.nodup_ofFn_ofInjective
    intro a b h
    exact eq_of_heq (Sigma.ext_iff.mp (Sum.inl.inj h)).2
  · simp [portList]

abbrev FactorFibre (f : CloneFactor E T) := {p : ClausePort E T // portFactor E T p=f}

theorem factor_fibre_card (s : V→Bool) (f : CloneFactor E T) :
    Nat.card (FactorFibre E T f)=(clonedClause E T s f).length := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
  have he : Finset.univ.filter (fun p : ClausePort E T=>portFactor E T p=f) =
      (portList E T f).toFinset := by
    ext p
    simp [mem_port_list]
  rw [he,List.toFinset_card_of_nodup (port_list_nodup E T f),
    ←actual_clause_ports E T s f,List.length_map]

theorem factor_fibre_degree (f : CloneFactor E T) :
    1≤Nat.card (FactorFibre E T f) ∧ Nat.card (FactorFibre E T f)≤3 := by
  rw [factor_fibre_card E T (fun _=>false)]
  exact cloned_clause_width E T _ f

noncomputable def scopePorts (f : CloneFactor E T) : List (FactorFibre E T f) :=
  (portList E T f).attach.map (fun p=>⟨p.val,(mem_port_list E T p.val f).mp p.property⟩)

theorem scope_projects (f : CloneFactor E T) :
    (scopePorts E T f).map Subtype.val = portList E T f := by
  rw [scopePorts,List.map_map]
  exact List.attach_map_subtype_val _

noncomputable def scopeEval (s : V→Bool) (f : CloneFactor E T)
    (b : FactorFibre E T f→Bool) : Bool :=
  (scopePorts E T f).any (fun p=>b p == portSign E T s p.val)

theorem scope_eval_on_variables (s : V→Bool) (f : CloneFactor E T)
    (b : Port E T→Bool) :
    scopeEval E T s f (fun p=>b (portOwner E T p.val)) =
      (clonedClause E T s f).eval b := by
  rw [←actual_clause_ports E T s f,Std.Sat.CNF.Clause.eval]
  simp only [List.any_map,scopeEval]
  have h := congrArg (List.any (p:=fun p : ClausePort E T=>
    b (portOwner E T p) == portSign E T s p)) (scope_projects E T f)
  change ((scopePorts E T f).map Subtype.val).any _ = (portList E T f).any _ at h
  rw [List.any_map] at h
  exact h

theorem all_cloned_clauses (s : V→Bool) (b : Port E T→Bool) :
    (cloneCNF E T s).Sat b ↔ ∀ f,(clonedClause E T s f).eval b=true := by
  simp [Std.Sat.CNF.sat_def,Std.Sat.CNF.eval,cloneCNF,List.all_eq_true]

#print axioms port_list_nodup
#print axioms factor_fibre_card
#print axioms factor_fibre_degree
#print axioms scope_projects
#print axioms scope_eval_on_variables
#print axioms all_cloned_clauses
end Paper5.AlwaysSatOriginal.Physical