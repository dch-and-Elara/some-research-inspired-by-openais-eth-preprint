import V8PooledRangeOrigin
import J6R12RepackBoolean
import J6R10RepackState

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

namespace V8PooledMenu
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive

section BinaryRoot
variable {W A B : Type*} {N : Network W A B} {f : ℤ[X]}

/-- Original tables are actual zero/one entries at their fixed creation
tag. No packet-produced entry is reclassified as a binary tensor. -/
noncomputable def binaryFile (f : ℤ[X]) (p₀ : ℕ)
    (flag : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool) : EntryFile f 1 N :=
  fun v => ⟨p₀,fun x => if flag v x then 1 else 0⟩

theorem read_binary (p₀ : ℕ) (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree)
    (flag : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool)
    (v : A ⊕ B) (x : ParentPorts N v → Bool) (p : ℕ) :
    ((binaryFile f p₀ flag) v).read hf p x = if flag v x then 1 else 0 := by
  change reduce p f 1 (canonicalLift p₀ f hf 1 (if flag v x then 1 else 0)) = _
  rw [J6R12Repack.canonical_lift_bool p₀ hp₀ f hf hd 1 (by decide)]
  cases flag v x <;> simp

variable {G : Type*} [LinearOrder G] [Fintype G] [Fintype A] [Fintype B] {a : ℕ}

noncomputable def oldScalar (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (flag : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool) (v : PhysicalState P i g) : TwoLocal :=
  ∏ u : Old (atGroup P i) g,
    if flag u.val (restrictOriginal N (atGroup P i) g u ((stateEquiv P i g).symm v)) then 1 else 0

theorem oldScalar_map (P : PhysicalPacking N a G) (i : Fin a) (g : G) (p₀ p : ℕ)
    (hp₀ : 0<p₀) (hf : f.Monic) (hd : 0<f.natDegree)
    (flag : ∀ v : A ⊕ B, (ParentPorts N v → Bool) → Bool) (v : PhysicalState P i g)
    (ψ : TwoLocal →+* Residue f 1 p) :
    ψ (oldScalar P i g flag v) = oldState P i g p (binaryFile f p₀ flag) hf v := by
  unfold oldScalar oldState
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro u _
  rw [read_binary p₀ hp₀ hf hd]
  split <;> simp

end BinaryRoot

namespace FiveCopy
open V8PooledRange V8PooledRange.NativeOrigin

variable {V E : Type*}

abbrev RawOld (V E : Type*) := ClauseId V E ⊕ Variable V

theorem clausePort_sign_fixed (G : Graph V E) (p : ThreePorts G)
    (s s' : V → Bool) (q : Occ V E) :
    clausePort G p s q = clausePort G p s' q := by
  rcases q with ⟨((⟨v,j⟩ | v) | (e | ⟨⟩)),b⟩ <;> cases b <;> rfl

def variableOf (G : Graph V E) (p : ThreePorts G) (q : Occ V E) : Variable V :=
  clausePort G p (fun _ => false) q

/-- Actual fixed-density lowering: every original occurrence has a
subdivision vertex, and its two wires reach its original clause and its
logical variable's equality tensor. This network does not depend on signs. -/
def network (G : Graph V E) (p : ThreePorts G) :
    Network (Edge V E) (RawOld V E) (Occ V E) where
  row w := if w.2 then .inr (variableOf G p w.1) else .inl w.1.1
  col w := w.1

abbrev VarInc (G : Graph V E) (p : ThreePorts G) (x : Variable V) :=
  {q : Occ V E // variableOf G p q = x}

def varPort (G : Graph V E) (p : ThreePorts G) (x : Variable V) (q : VarInc G p x) :
    ParentPorts (network G p) (.inl (.inr x)) :=
  ⟨.inl (q.val,true),congrArg (fun x => Sum.inl (Sum.inr x)) q.property⟩

def varPortEquiv (G : Graph V E) (p : ThreePorts G) (x : Variable V) :
    VarInc G p x ≃ ParentPorts (network G p) (.inl (.inr x)) where
  toFun := varPort G p x
  invFun
    | ⟨.inl (q,true),h⟩ => ⟨q,Sum.inr.inj (Sum.inl.inj h)⟩
    | ⟨.inl (_,false),h⟩ => nomatch h
    | ⟨.inr _,h⟩ => nomatch h
  left_inv _ := rfl
  right_inv
    | ⟨.inl (_,true),_⟩ => rfl
    | ⟨.inl (_,false),h⟩ => nomatch h
    | ⟨.inr _,h⟩ => nomatch h

def clauseInc (G : Graph V E) (p : ThreePorts G) (i : ClauseId V E) (b : Bool) :
    ParentPorts (network G p) (.inl (.inl i)) :=
  ⟨.inl ((i,b),false),rfl⟩

def subdivInc (G : Graph V E) (p : ThreePorts G) (q : Occ V E) (b : Bool) :
    ParentPorts (network G p) (.inr q) :=
  ⟨.inr (q,b),rfl⟩

/-- All three kinds of raw binary tensors from the same five-copy formula. -/
noncomputable def flags (G : Graph V E) (p : ThreePorts G) (s : V → Bool) :
    ∀ v : RawOld V E ⊕ Occ V E, (ParentPorts (network G p) v → Bool) → Bool
  | .inl (.inl i), x =>
    decide (x (clauseInc G p i false) = (clauses G p s i).1.2 ∨
      x (clauseInc G p i true) = (clauses G p s i).2.2)
  | .inl (.inr v), x =>
    decide (∀ a b : VarInc G p v, x (varPort G p v a) = x (varPort G p v b))
  | .inr q, x =>
    decide (x (subdivInc G p q false) = x (subdivInc G p q true))

def rootPrec (V : Type*) [Fintype V] : ℕ := 5*Fintype.card V+3

theorem rootPrec_pos (V : Type*) [Fintype V] : 0<rootPrec V := by
  unfold rootPrec
  omega

noncomputable def file [Fintype V] (f : ℤ[X])
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool) :
    EntryFile f 1 (network G p) :=
  binaryFile f (rootPrec V) (flags G p s)

theorem clause_flag_eq (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (x : Edge V E → Bool) (i : ClauseId V E) :
    flags G p s (.inl (.inl i)) (assignment (network G p) x (.inl (.inl i))) = true ↔
      x ((i,false),false) = (clauses G p s i).1.2 ∨
      x ((i,true),false) = (clauses G p s i).2.2 := by
  simp only [flags,decide_eq_true_eq]
  rfl

theorem subdiv_flag_eq (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (x : Edge V E → Bool) (q : Occ V E) :
    flags G p s (.inr q) (assignment (network G p) x (.inr q)) = true ↔
      x (q,false) = x (q,true) := by
  simp only [flags,decide_eq_true_eq]
  rfl

theorem var_flag_eq (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (x : Edge V E → Bool) (v : Variable V) :
    flags G p s (.inl (.inr v)) (assignment (network G p) x (.inl (.inr v))) = true ↔
      ∀ q r : VarInc G p v, x (q.val,true) = x (r.val,true) := by
  simp only [flags,decide_eq_true_eq]
  rfl

/-- The ordinary raw tensors on this actual network recognize exactly
the wire assignments counted by the frozen C6 theorem. -/
theorem flags_eq_origin (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (x : Edge V E → Bool) :
    (∀ v, flags G p s v (assignment (network G p) x v) = true) ↔
      Satisfied G p s x := by
  constructor
  · intro h
    refine ⟨fun q => (subdiv_flag_eq G p s x q).mp (h (.inr q)), ?_,
      fun i => (clause_flag_eq G p s x i).mp (h (.inl (.inl i)))⟩
    intro q r he
    let v := variableOf G p q
    have hr : variableOf G p r = v := by
      change clausePort G p (fun _ => false) r = clausePort G p (fun _ => false) q
      exact (clausePort_sign_fixed G p _ s r).trans (he.symm.trans (clausePort_sign_fixed G p s _ q))
    exact (var_flag_eq G p s x v).mp (h (.inl (.inr v))) ⟨q,rfl⟩ ⟨r,hr⟩
  · rintro ⟨hs,hv,hc⟩ (v|q)
    · rcases v with (i|v)
      · exact (clause_flag_eq G p s x i).mpr (hc i)
      · apply (var_flag_eq G p s x v).mpr
        intro q r
        apply hv
        rw [clausePort_sign_fixed G p s (fun _ => false) q.val,
          clausePort_sign_fixed G p s (fun _ => false) r.val]
        exact q.property.trans r.property.symm
    · exact (subdiv_flag_eq G p s x q).mpr (hs q)

#print axioms clausePort_sign_fixed
#print axioms varPortEquiv
#print axioms flags_eq_origin
end FiveCopy
#print axioms read_binary
#print axioms oldScalar_map
end V8PooledMenu
