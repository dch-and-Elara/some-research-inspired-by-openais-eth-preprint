import P5AlwaysSatOriginalPhysicalMAIN
import P5MainBalanceM6Origin

/-! Literal direct/sparse MAIN chart of the same (M.7) clone. Every
scoped row and its signed pin come from an actual source incidence. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainIterator P5MainBalance.M6
open scoped Classical

variable {V X F Copy I B : Type*} [Fintype V] [LinearOrder B]
variable {E : Finset (V×V)} {T : Finset V}

structure ClauseChart
    (E : Finset (V×V)) (T : Finset V) (X F Copy I B : Type*) [LinearOrder B] where
  layout : SourceLayout X (Port E T) F Copy I B
  inc : ClausePort E T ↪ X
  fac : CloneFactor E T ↪ F
  owner_route : ∀ p,layout.placement.owner (inc p)=portOwner E T p
  factor_route : ∀ p,layout.factor (inc p)=fac (portFactor E T p)

def ClauseChart.mark (C : ClauseChart E T X F Copy I B) : V ↪ X :=
  (marked E T).trans C.inc

@[simp] theorem ClauseChart.pin_factor (C : ClauseChart E T X F Copy I B) (v : V) :
    signedOwner C.layout C.mark v=C.fac (.inl (.inl v)) :=
  (C.factor_route (marked E T v)).trans (congrArg C.fac (marked_factor E T v))

abbrev ClauseChart.Signs (C : ClauseChart E T X F Copy I B) (f : CloneFactor E T) :=
  {v : V // signedOwner C.layout C.mark v=C.fac f}→Bool

def ClauseChart.scoped (C : ClauseChart E T X F Copy I B) (f : CloneFactor E T)
    (p : FactorFibre E T f) : {e : X // C.layout.factor e=C.fac f} :=
  ⟨C.inc p.val,(C.factor_route p.val).trans (congrArg C.fac p.property)⟩

noncomputable def ClauseChart.literals (_C : ClauseChart E T X F Copy I B)
    (f : CloneFactor E T) : List (FactorFibre E T f) := scopePorts E T f

theorem ClauseChart.literal_count (C : ClauseChart E T X F Copy I B)
    (s : V→Bool) (f : CloneFactor E T) :
    (C.literals f).length=(clonedClause E T s f).length := by
  calc
    _ = (portList E T f).length := by
        exact (List.length_map (f:=Subtype.val) (as:=scopePorts E T f)).symm.trans
          (congrArg List.length (scope_projects E T f))
    _ = _ := (List.length_map (f:=fun p=>(portOwner E T p,portSign E T s p))
      (as:=portList E T f)).symm.trans (congrArg List.length (actual_clause_ports E T s f))

theorem ClauseChart.literal_count_le (C : ClauseChart E T X F Copy I B)
    (f : CloneFactor E T) : (C.literals f).length≤3 := by
  rw [C.literal_count (fun _=>false) f]
  exact (cloned_clause_width E T _ f).2

noncomputable def ClauseChart.extendSigns (C : ClauseChart E T X F Copy I B)
    (f : CloneFactor E T) (s : C.Signs f) : V→Bool :=
  fun v=>if h : signedOwner C.layout C.mark v=C.fac f then s ⟨v,h⟩ else false

noncomputable def ClauseChart.localSign (C : ClauseChart E T X F Copy I B)
    (f : CloneFactor E T) (s : C.Signs f) (p : FactorFibre E T f) : Bool :=
  portSign E T (C.extendSigns f s) p.val

private theorem sign_at_pin_only (p : ClausePort E T) (σ τ : V→Bool)
    (h : ∀ v,portFactor E T p=.inl (.inl v)→τ v=σ v) :
    portSign E T τ p=portSign E T σ p := by
  rcases p with ⟨i,j⟩|⟨p,b⟩
  · rcases i with v|(e|(_|⟨v,b⟩))
    · have hi : j=⟨0,by change 0<1; decide⟩ := by
        apply Fin.ext
        have hh := j.isLt
        change j.val<1 at hh
        exact Nat.lt_one_iff.mp hh
      subst j
      exact h v rfl
    · rfl
    · rfl
    · cases b <;> rfl
  · rfl

@[simp] theorem ClauseChart.local_sign_global (C : ClauseChart E T X F Copy I B)
    (f : CloneFactor E T) (σ : V→Bool) (p : FactorFibre E T f) :
    C.localSign f (fun v=>σ v.val) p=portSign E T σ p.val := by
  apply sign_at_pin_only
  intro v h
  unfold ClauseChart.extendSigns
  rw [dif_pos ?_]
  exact (C.pin_factor v).trans (congrArg C.fac (h.symm.trans p.property))

theorem ClauseChart.literal_word_global (C : ClauseChart E T X F Copy I B)
    (f : CloneFactor E T) (σ : V→Bool) :
    (C.literals f).map (fun p=>(portOwner E T p.val,C.localSign f (fun v=>σ v.val) p)) =
      clonedClause E T σ f := by
  simp only [C.local_sign_global]
  rw [←actual_clause_ports E T σ f,←scope_projects E T f,List.map_map]
  rfl

noncomputable def ClauseChart.localEval (C : ClauseChart E T X F Copy I B)
    (f : CloneFactor E T) (s : C.Signs f) (x : Port E T→Bool) : Bool :=
  (C.literals f).any (fun p=>x (C.layout.placement.owner (C.inc p.val)) == C.localSign f s p)

theorem ClauseChart.local_eval_global (C : ClauseChart E T X F Copy I B)
    (f : CloneFactor E T) (σ : V→Bool) (x : Port E T→Bool) :
    C.localEval f (fun v=>σ v.val) x=(clonedClause E T σ f).eval x := by
  unfold ClauseChart.localEval
  simp only [C.owner_route,C.local_sign_global]
  exact scope_eval_on_variables E T σ f x

def directChart
    (L : SourceLayout (ClausePort E T) (Port E T) (CloneFactor E T) Copy I B)
    (ho : L.placement.owner=portOwner E T) (hf : L.factor=portFactor E T) :
    ClauseChart E T (ClausePort E T) (CloneFactor E T) Copy I B where
  layout := L
  inc := Function.Embedding.refl _
  fac := Function.Embedding.refl _
  owner_route _ := congrFun ho _
  factor_route _ := congrFun hf _

def sparseChart
    (L : SourceLayout (SparsePort E T) (Port E T) (SparseFactor E T) Copy I B)
    (ho : L.placement.owner=sparseOwner E T) (hf : L.factor=sparseFactor E T) :
    ClauseChart E T (SparsePort E T) (SparseFactor E T) Copy I B where
  layout := L
  inc := Function.Embedding.inl
  fac := Function.Embedding.inl
  owner_route _ := congrFun ho _
  factor_route _ := congrFun hf _

theorem direct_chart_mark
    (L : SourceLayout (ClausePort E T) (Port E T) (CloneFactor E T) Copy I B)
    (ho) (hf) : (directChart L ho hf).mark=marked E T := by
  ext v
  rfl

theorem sparse_chart_mark
    (L : SourceLayout (SparsePort E T) (Port E T) (SparseFactor E T) Copy I B)
    (ho) (hf) : (sparseChart L ho hf).mark=sparseMarked E T := by
  ext v
  rfl

#print axioms ClauseChart.pin_factor
#print axioms ClauseChart.literal_count
#print axioms ClauseChart.literal_count_le
#print axioms ClauseChart.local_sign_global
#print axioms ClauseChart.local_eval_global
#print axioms ClauseChart.literal_word_global
#print axioms direct_chart_mark
#print axioms sparse_chart_mark
end Paper5.AlwaysSatOriginal.Physical.Taylor