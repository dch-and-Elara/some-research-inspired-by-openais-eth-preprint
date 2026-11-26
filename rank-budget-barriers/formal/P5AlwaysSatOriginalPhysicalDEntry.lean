import P5AlwaysSatOriginalPhysicalDNetwork
import J6R10RepackPrecision

/-! Literal bounded-degree Appendix D root truth tables. Equality at the
one-port b₀ attachment is free, and no arbitrary truth receipt is taken. -/
namespace Paper5.AlwaysSatOriginal.Physical
open scoped BigOperators Classical Polynomial
open J6R10Repack J6R9Recursive
variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

abbrev DNodes := DVertex E T ⊕ ClausePort E T

abbrev CopyFibre (v : Port E T) := {e : ClausePort E T // portOwner E T e=v}

def variableWire (v : Port E T) (p : CopyFibre E T v) :
    ParentPorts (dNetwork E T) (.inl (.inl v)) :=
  ⟨.inl (p.val,false),congrArg Sum.inl (by simpa [dNetwork] using p.property)⟩

def factorWire (f : CloneFactor E T) (p : FactorFibre E T f) :
    ParentPorts (dNetwork E T) (.inl (.inr f)) :=
  ⟨.inl (p.val,true),congrArg Sum.inl (by simpa [dNetwork] using p.property)⟩

def equalityWire (p : ClausePort E T) (b : Bool) :
    ParentPorts (dNetwork E T) (.inr p) := ⟨.inr (p,b),rfl⟩

def reference (v : Port E T) : CopyFibre E T v := ⟨.inl v,rfl⟩

noncomputable def dTable (s : V→Bool) :
    (v : DNodes E T)→(ParentPorts (dNetwork E T) v→Bool)→Bool
  | .inl (.inl v),x => decide (∀ e : CopyFibre E T v,
      x (variableWire E T v e)=x (variableWire E T v (reference E T v)))
  | .inl (.inr f),x => scopeEval E T s f (fun p=>x (factorWire E T f p))
  | .inr p,x => x (equalityWire E T p false)==x (equalityWire E T p true)

noncomputable def dFlag (s : V→Bool) (q : DWire E T→Bool) (v : DNodes E T) :=
  dTable E T s v (J6R10Repack.assignment (dNetwork E T) q v)

theorem d_var_flag (s : V→Bool) (q : DWire E T→Bool) (v : Port E T) :
    dFlag E T s q (.inl (.inl v))=true ↔
      ∀ e : CopyFibre E T v,q (e.val,false)=q (.inl v,false) := by
  exact decide_eq_true_iff

theorem d_clause_flag (s : V→Bool) (q : DWire E T→Bool) (f : CloneFactor E T) :
    dFlag E T s q (.inl (.inr f)) =
      scopeEval E T s f (fun e=>q (e.val,true)) := rfl

theorem d_subdiv_flag (s : V→Bool) (q : DWire E T→Bool) (p : ClausePort E T) :
    dFlag E T s q (.inr p)=true ↔ q (p,false)=q (p,true) := by
  exact beq_iff_eq

noncomputable def dLift (a : Port E T→Bool) : DWire E T→Bool := fun e=>a (portOwner E T e.1)
def dProject (q : DWire E T→Bool) : Port E T→Bool := fun v=>q (.inl v,false)

@[simp] theorem d_project_lift (a : Port E T→Bool) : dProject E T (dLift E T a)=a := rfl

abbrev DAccept (s : V→Bool) (q : DWire E T→Bool) : Prop :=
  ∀ v,dFlag E T s q v=true

theorem d_lift_accept_iff (s : V→Bool) (a : Port E T→Bool) :
    DAccept E T s (dLift E T a) ↔ (cloneCNF E T s).Sat a := by
  rw [all_cloned_clauses]
  constructor
  · intro h f
    have ht := h (.inl (.inr f))
    rwa [d_clause_flag,show (fun e : FactorFibre E T f=>dLift E T a (e.val,true)) =
      (fun e=>a (portOwner E T e.val)) from rfl,scope_eval_on_variables] at ht
  · intro h v
    rcases v with (v|f)|e
    · apply (d_var_flag E T s _ v).mpr
      intro e
      exact congrArg a e.property
    · rw [d_clause_flag,show (fun e : FactorFibre E T f=>dLift E T a (e.val,true)) =
        (fun e=>a (portOwner E T e.val)) from rfl,scope_eval_on_variables]
      exact h f
    · apply (d_subdiv_flag E T s _ e).mpr
      rfl

theorem d_accepted_lift_project (s : V→Bool) (q : DWire E T→Bool)
    (hq : DAccept E T s q) : dLift E T (dProject E T q)=q := by
  funext w
  obtain ⟨p,b⟩ := w
  let v := portOwner E T p
  have hv := (d_var_flag E T s q v).mp (hq (.inl (.inl v))) ⟨p,rfl⟩
  have hp := (d_subdiv_flag E T s q p).mp (hq (.inr p))
  cases b
  · exact hv.symm
  · exact hv.symm.trans hp

noncomputable def d_model_equiv (s : V→Bool) :
    {a : Port E T→Bool // (cloneCNF E T s).Sat a} ≃
      {q : DWire E T→Bool // DAccept E T s q} where
  toFun a := ⟨dLift E T a.val,(d_lift_accept_iff E T s a.val).mpr a.property⟩
  invFun q := ⟨dProject E T q.val,(d_lift_accept_iff E T s _).mp
    ((d_accepted_lift_project E T s q.val q.property).symm ▸ q.property)⟩
  left_inv _ := Subtype.ext rfl
  right_inv q := Subtype.ext (d_accepted_lift_project E T s q.val q.property)

noncomputable def dEntryFile (s : V→Bool) (f : ℤ[X]) (ell p : ℕ) :
    EntryFile f ell (dNetwork E T) :=
  fun v=>⟨p,fun b=>if dTable E T s v b then 1 else 0⟩

theorem d_entry_created (s : V→Bool) (f : ℤ[X]) (ell p : ℕ) (v : DNodes E T) :
    (dEntryFile E T s f ell p v).created=p := rfl

theorem d_gate_at_creation (s : V→Bool) (f : ℤ[X]) (ell p : ℕ)
    (hf : f.Monic) (q : DWire E T→Bool) (v : DNodes E T) :
    reduce p f ell ((dEntryFile E T s f ell p v).frozen hf
      (J6R10Repack.assignment (dNetwork E T) q v)) =
        if dFlag E T s q v then 1 else 0 :=
  (dEntryFile E T s f ell p v).read_created hf _

private theorem prod_of_truth {A R : Type*} [Fintype A] [CommSemiring R] (b : A→Bool) :
    (∏ a : A,if b a then (1:R) else 0)=if ∀ a,b a=true then 1 else 0 := by
  classical
  by_cases h : ∀ a,b a=true
  · simp [h]
  · rw [if_neg h]
    obtain ⟨a,ha⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ a)
    simp only [if_neg ha]

private theorem sum_of_truth {A R : Type*} [Fintype A] [Semiring R] (b : A→Prop)
    [DecidablePred b] :
    (∑ a : A,if b a then (1:R) else 0)=(Nat.card {a : A // b a}:R) := by
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,←Finset.sum_filter]
  simp

theorem d_receives_cloned_count (s : V→Bool) (f : ℤ[X]) (ell p : ℕ)
    (hf : f.Monic) :
    reduce p f ell (trueContraction (dNetwork E T) (dEntryFile E T s f ell p) hf) =
      (PinnedCNF.modelCount (cloneCNF E T s):Residue f ell p) := by
  let C := cloneCNF E T s
  have hcount : Nat.card {a : Port E T→Bool // C.Sat a}=PinnedCNF.modelCount C := by
    rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
    unfold PinnedCNF.modelCount
    congr 1
    ext a
    simp [Std.Sat.CNF.sat_def]
  unfold trueContraction
  rw [map_sum]
  calc
    _ = ∑ q : DWire E T→Bool,∏ v : DNodes E T,
        if dFlag E T s q v then (1:Residue f ell p) else 0 := by
      apply Finset.sum_congr (Finset.ext (fun _=>by simp only [Finset.mem_univ]))
      intro q _
      rw [map_prod]
      exact Finset.prod_congr (Finset.ext (fun _=>by simp only [Finset.mem_univ]))
        (fun v _=>d_gate_at_creation E T s f ell p hf q v)
    _ = ∑ q : DWire E T→Bool,if DAccept E T s q then (1:Residue f ell p) else 0 := by
      exact Finset.sum_congr rfl (fun q _=>prod_of_truth _)
    _ = (Nat.card {q : DWire E T→Bool // DAccept E T s q}:Residue f ell p) :=
      sum_of_truth _
    _ = _ := by
      rw [Nat.card_congr (d_model_equiv E T s).symm,hcount]

theorem d_receives_original_M7 (s : V→Bool) (f : ℤ[X]) (ell p : ℕ)
    (hf : f.Monic) :
    reduce p f ell (trueContraction (dNetwork E T) (dEntryFile E T s f ell p) hf) =
      ((2^(1+∑ v∈T,if s v then (1:ℕ) else 0)+
        PinnedCNF.modelCount (PinnedCNF.formula E s):ℕ):Residue f ell p) := by
  rw [d_receives_cloned_count E T s f ell p hf,cloned_display_M7]

#print axioms d_var_flag
#print axioms d_clause_flag
#print axioms d_subdiv_flag
#print axioms d_lift_accept_iff
#print axioms d_accepted_lift_project
#print axioms d_model_equiv
#print axioms d_entry_created
#print axioms d_gate_at_creation
#print axioms d_receives_cloned_count
#print axioms d_receives_original_M7
end Paper5.AlwaysSatOriginal.Physical