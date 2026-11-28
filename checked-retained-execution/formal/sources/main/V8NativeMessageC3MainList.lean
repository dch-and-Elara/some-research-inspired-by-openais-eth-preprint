import V8NativeMessageC3MainAddress

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3700000

/-! C3's real five-copy binary clause factors. The point arguments
are computed from a legal public address and a genuine local point
by the source substitution, not assigned arbitrary values. -/
namespace V8NativeMessage.C3.RawMain
open scoped Classical BigOperators Polynomial
open Polynomial V8PooledRange
noncomputable section

variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ]
variable {G : Graph V E} {p : ThreePorts G}

def switchClause (v : V) : ClauseId V E := .inl (.inr v)

omit [Fintype V] [Fintype E] [Fintype Γ] in
theorem clause_ports_are_fixed (s : V→Bool) (f : ClauseId V E) :
    (clauses G p s f).1.1=(clauses G p (fun _=>false) f).1.1 ∧
    (clauses G p s f).2.1=(clauses G p (fun _=>false) f).2.1 := by
  rcases f with ((a|v)|(e|u)) <;> exact ⟨rfl,rfl⟩

structure FiveFile (G : Graph V E) (p : ThreePorts G) where
  layout : Layout V E Γ
  hasScope : ∀ f : ClauseId V E,
    (clauses G p (fun _=>false) f).1.1 ∈ layout.scope f ∧
    (clauses G p (fun _=>false) f).2.1 ∈ layout.scope f

variable (F : FiveFile (Γ:=Γ) G p) (a : Address F.layout) (κ : ℕ)


theorem true_ports_in_scope (s : V→Bool) (f : ClauseId V E) :
    (clauses G p s f).1.1 ∈ F.layout.scope f ∧ (clauses G p s f).2.1 ∈ F.layout.scope f := by
  rw [(clause_ports_are_fixed (G:=G) (p:=p) s f).1,
    (clause_ports_are_fixed (G:=G) (p:=p) s f).2]
  exact F.hasScope f

def literal {R : Type*} [CommRing R] (s : Bool) (x : R) : R := if s then x else 1-x

def clauseJet (s : V→Bool) (g : Γ) (x : Fibre F.layout a g) (f : ClauseId V E) : C3.Jet ℚ κ :=
  let c := clauses G p s f
  1-(1-literal c.1.2 (theta F.layout a g x κ f c.1.1)) *
    (1-literal c.2.2 (theta F.layout a g x κ f c.2.1))

def leftTheta (g : Γ) (x : Fibre F.layout a g) (v : V) : C3.Jet ℚ κ :=
  theta F.layout a g x κ (switchClause (E:=E) v) (.inl (v,0))

def rightTheta (g : Γ) (x : Fibre F.layout a g) (v : V) : C3.Jet ℚ κ :=
  theta F.layout a g x κ (switchClause (E:=E) v) (.inl (v,2))

theorem switchClause_literal_jet (s : V→Bool) (g : Γ) (x : Fibre F.layout a g) (v : V) :
    clauseJet F a κ s g x (switchClause v) =
      C3.switch (s v) (leftTheta F a κ g x v) (rightTheta F a κ g x v) := by
  simp [clauseJet,switchClause,clauses,literal,C3.switch,leftTheta,rightTheta]

def inGroup (g : Γ) (f : ClauseId V E) : Prop := F.layout.factorGroup a.t f=g

def conditionedClauseJet (s : V→Bool) (g : Γ) (x : Fibre F.layout a g) (f : ClauseId V E) : C3.Jet ℚ κ :=
  if inGroup F a g f then clauseJet F a κ s g x f else 1

def actualPoint (s : V→Bool) (g : Γ) (x : Fibre F.layout a g) : C3.Jet ℚ κ :=
  ∏ f, conditionedClauseJet F a κ s g x f

def staticFactor (g : Γ) (x : Fibre F.layout a g) : C3.Jet ℚ κ :=
  (∏ q : V×Fin 5, conditionedClauseJet F a κ (fun _=>false) g x (.inl (.inl q))) *
  ∏ q : E⊕Unit, conditionedClauseJet F a κ (fun _=>false) g x (.inr q)

theorem right_clauses_static (s : V→Bool) (g : Γ) (x : Fibre F.layout a g) (c : E⊕Unit) :
    conditionedClauseJet F a κ s g x (.inr c) =
      conditionedClauseJet F a κ (fun _=>false) g x (.inr c) := by
  cases c <;> rfl

theorem cycle_clauses_static (s : V→Bool) (g : Γ) (x : Fibre F.layout a g) (q : V×Fin 5) :
    conditionedClauseJet F a κ s g x (.inl (.inl q)) =
      conditionedClauseJet F a κ (fun _=>false) g x (.inl (.inl q)) := rfl

def owner (v : V) : Γ := F.layout.factorGroup a.t (switchClause v)

theorem switch_list_eq (s : V→Bool) (g : Γ) (x : Fibre F.layout a g) :
    (∏ v : V, conditionedClauseJet F a κ s g x (switchClause v)) =
      ∏ v : {v // owner F a v=g},
        C3.switch (s v.val) (leftTheta F a κ g x v.val) (rightTheta F a κ g x v.val) := by
  let U := Finset.univ.filter (fun v : V => owner F a v=g)
  have hU (v : V) : v∈U ↔ owner F a v=g := by simp [U]
  rw [← Finset.prod_subtype U hU (fun v => C3.switch (s v) (leftTheta F a κ g x v)
    (rightTheta F a κ g x v))]
  rw [show U=Finset.univ.filter (fun v : V => owner F a v=g) from rfl,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro v _
  simp only [conditionedClauseJet,inGroup,owner,switchClause_literal_jet]

theorem actualPoint_split (s : V→Bool) (g : Γ) (x : Fibre F.layout a g) :
    actualPoint F a κ s g x =
      staticFactor F a κ g x * ∏ v : {v // owner F a v=g},
        C3.switch (s v.val) (leftTheta F a κ g x v.val) (rightTheta F a κ g x v.val) := by
  unfold actualPoint staticFactor
  rw [Fintype.prod_sum_type,Fintype.prod_sum_type]
  simp only [cycle_clauses_static,right_clauses_static]
  rw [← switch_list_eq F a κ s g x]
  change (_ * (∏ v : V, conditionedClauseJet F a κ s g x (.inl (.inr v)))) * _ = _
  unfold switchClause
  ac_rfl

variable {b : Γ→ℕ}
structure NativePrivateLists (b : Γ→ℕ) where
  point : ∀ g, Fin (b g) → Fibre F.layout a g
  weight : ∀ g, Fin (b g)→C3.Jet ℚ κ

variable (Q : NativePrivateLists F a κ b)

def toFixedLists : C3.MainLists (V:=V) (J:=C3.Jet ℚ κ) b where
  owner := owner F a
  fixed g k := Q.weight g k * staticFactor F a κ g (Q.point g k)
  θ₁ g k v := leftTheta F a κ g (Q.point g k) v
  θ₂ g k v := rightTheta F a κ g (Q.point g k) v

def actualRegister (s : V→Bool) : C3.Jet ℚ κ :=
  ∏ g, ∑ k : Fin (b g), Q.weight g k * actualPoint F a κ s g (Q.point g k)

theorem native_private_point (s : V→Bool) (g : Γ) (k : Fin (b g)) :
    C3.mainPoint (toFixedLists F a κ Q) s g k =
      Q.weight g k * actualPoint F a κ s g (Q.point g k) := by
  rw [actualPoint_split]
  unfold C3.mainPoint toFixedLists
  rw [mul_assoc]

theorem native_private_register (s : V→Bool) :
    C3.mainCompleted (toFixedLists F a κ Q) s=actualRegister F a κ Q s := by
  unfold C3.mainCompleted actualRegister
  simp only [native_private_point]

#print axioms clause_ports_are_fixed
#print axioms true_ports_in_scope
#print axioms switchClause_literal_jet
#print axioms switch_list_eq
#print axioms actualPoint_split
#print axioms native_private_point
#print axioms native_private_register
end
end V8NativeMessage.C3.RawMain