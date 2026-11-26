import P5HybridDUnclonedGraph

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 18000000
set_option maxRecDepth 1800

/-! The literal bounded-size Boolean tables on the two old trivalent
equality vertices, the original clauses, and the subdivision vertices.
The internal wire is counted as a real source variable in the contraction,
but is not an extra degree of freedom in its satisfying assignments. -/
namespace Paper5.HybridDUncloned
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R9Recursive

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree F v=3)
local notation "N" => network F cubic

def truth (σ : W→Bool) : ∀ v : Old F⊕Link F,(ParentPorts N v→Bool)→Bool
  | .inl (.inl u), x => decide (∀ p q : ParentPorts N (.inl (.inl u)),x p=x q)
  | .inl (.inr (.inl v)), x => decide (x ⟨.inl (pinWire F v),rfl⟩=σ v)
  | .inl (.inr (.inr e)), x =>
      x ⟨.inl (.inl (.inr (e,false)),true),rfl⟩ ||
      x ⟨.inl (.inl (.inr (e,true)),true),rfl⟩
  | .inr e, x => decide (x ⟨.inr (e,false),rfl⟩=x ⟨.inr (e,true),rfl⟩)

def file (f : ℤ[X]) (p : ℕ) (σ : W→Bool) : EntryFile f 1 N :=
  fun v=>⟨p,fun x=>if truth F cubic σ v x then 1 else 0⟩

theorem file_creation (f : ℤ[X]) (p : ℕ) (σ : W→Bool) (v : Old F⊕Link F) :
    (file F cubic f p σ v).created=p := rfl

theorem pin_file_local (f : ℤ[X]) (p : ℕ) (σ σ' : W→Bool) (v : W)
    (h : σ v=σ' v) :
    file F cubic f p σ (.inl (.inr (.inl v)))=
    file F cubic f p σ' (.inl (.inr (.inl v))) := by
  simp [file,truth,h]

theorem nonpin_file_unchanged (f : ℤ[X]) (p : ℕ) (σ σ' : W→Bool) (v : Old F⊕Link F)
    (h : ∀ w : W,v≠.inl (.inr (.inl w))) :
    file F cubic f p σ v=file F cubic f p σ' v := by
  rcases v with (u|w|e)|l
  · rfl
  · exact (h w rfl).elim
  · rfl
  · rfl

def linkVariable : Link F→W
  | .inl p => variableOf F cubic p
  | .inr v => v

def copyAssignment (σ : W→Bool) (e : Wire F) : Bool :=
  σ (linkVariable F cubic e.1)

def Accept (σ : W→Bool) (x : Wire F→Bool) : Prop :=
  ∀ v, truth F cubic σ v (assignment N x v)=true

theorem read_subdivision {σ : W→Bool} {x : Wire F→Bool}
    (h : Accept F cubic σ x) (e : Link F) : x (e,false)=x (e,true) := by
  have h0 := h (.inr e)
  change decide (x (e,false)=x (e,true))=true at h0
  exact of_decide_eq_true h0

theorem read_tree_port {σ : W→Bool} {x : Wire F→Bool}
    (h : Accept F cubic σ x) (u : Tree W) (e g : Wire F)
    (he : (N).row e=.inl u) (hg : (N).row g=.inl u) : x e=x g := by
  have h0 := h (.inl (.inl u))
  change decide (∀ p q : ParentPorts N (.inl (.inl u)),x (edge p.val)=x (edge q.val))=true at h0
  exact (of_decide_eq_true h0)
    ⟨.inl e,congrArg (fun y : Old F=>(.inl y : Old F⊕Link F)) he⟩
    ⟨.inl g,congrArg (fun y : Old F=>(.inl y : Old F⊕Link F)) hg⟩

theorem occurrence_reaches_bridge {σ : W→Bool} {x : Wire F→Bool}
    (h : Accept F cubic σ x) (p : Occ F) (b : Bool) :
    x (.inl p,b)=x (.inr (variableOf F cubic p),false) := by
  let u := (occSite F cubic p).1
  have ht : x (.inl p,false)=x (.inr u.1,u.2) :=
    read_tree_port F cubic h u _ _ rfl rfl
  have hBridge : x (.inr u.1,u.2)=x (.inr u.1,false) := by
    cases hb : u.2
    · rfl
    · exact (read_subdivision F cubic h (.inr u.1)).symm
  have hp : x (.inl p,b)=x (.inl p,false) := by
    cases b
    · rfl
    · exact (read_subdivision F cubic h (.inl p)).symm
  exact hp.trans (ht.trans hBridge)

theorem bridge_forced_by_pin {σ : W→Bool} {x : Wire F→Bool}
    (h : Accept F cubic σ x) (v : W) : x (.inr v,false)=σ v := by
  have h0 := h (.inl (.inr (.inl v)))
  change decide (x (pinWire F v)=σ v)=true at h0
  have link := occurrence_reaches_bridge F cubic h (.inl v) true
  change x (pinWire F v)=x (.inr v,false) at link
  exact link.symm.trans (of_decide_eq_true h0)

theorem all_wires_forced {σ : W→Bool} {x : Wire F→Bool}
    (h : Accept F cubic σ x) : x=copyAssignment F cubic σ := by
  funext w
  rcases w with ⟨(p|v),b⟩
  · exact (occurrence_reaches_bridge F cubic h p b).trans (bridge_forced_by_pin F cubic h _)
  · cases b
    · exact bridge_forced_by_pin F cubic h v
    · exact (read_subdivision F cubic h (.inr v)).symm.trans (bridge_forced_by_pin F cubic h v)

omit [Fintype W] in
theorem tree_owner_same_variable (u : Tree W) (p : ParentPorts N (.inl (.inl u))) :
    linkVariable F cubic (edge p.val).1=u.1 := by
  rcases p with ⟨p,h⟩
  rcases p with p|p
  · rcases p with ⟨(p|v),b⟩
    · cases b
      · exact congrArg Prod.fst (Sum.inl.inj (Sum.inl.inj h))
      · simp [owner,network] at h
    · exact congrArg Prod.fst (Sum.inl.inj (Sum.inl.inj h))
  · simp [owner] at h

theorem same_original_assignment (σ : W→Bool) (x : Wire F→Bool) :
    Accept F cubic σ x ↔ x=copyAssignment F cubic σ ∧ PinnedCNF.AllEdges F σ := by
  constructor
  · intro h
    have he := all_wires_forced F cubic h
    refine ⟨he,?_⟩
    intro e em
    have h0 := h (.inl (.inr (.inr ⟨e,em⟩)))
    change (x (.inl (.inr (⟨e,em⟩,false)),true) ||
      x (.inl (.inr (⟨e,em⟩,true)),true))=true at h0
    rw [he] at h0
    simpa only [copyAssignment,linkVariable,literal_left_endpoint,literal_right_endpoint,
      Bool.or_eq_true] using h0
  · rintro ⟨rfl,h⟩ v
    rcases v with (u|w|e)|l
    · change decide (∀ p q : ParentPorts N (.inl (.inl u)),
        copyAssignment F cubic σ (edge p.val)=copyAssignment F cubic σ (edge q.val))=true
      apply decide_eq_true
      intro p q
      unfold copyAssignment
      rw [tree_owner_same_variable F cubic u p,tree_owner_same_variable F cubic u q]
    · change decide (σ w=σ w)=true
      simp
    · change (copyAssignment F cubic σ (.inl (.inr (e,false)),true) ||
        copyAssignment F cubic σ (.inl (.inr (e,true)),true))=true
      simp only [copyAssignment,linkVariable,literal_left_endpoint,literal_right_endpoint,
        Bool.or_eq_true]
      exact h e.val e.property
    · change decide (σ (linkVariable F cubic l)=σ (linkVariable F cubic l))=true
      simp

theorem literal_contraction_is_uncloned_count
    (f : ℤ[X]) (hf : f.Monic) (p : ℕ) (σ : W→Bool) :
    reduce p f 1 (trueContraction N (file F cubic f p σ) hf) =
      (PinnedCNF.modelCount (PinnedCNF.formula F σ) : Residue f 1 p) := by
  classical
  unfold trueContraction
  rw [map_sum,PinnedCNF.count_eq_indicator]
  trans ∑ x : Wire F→Bool, if Accept F cubic σ x then (1:Residue f 1 p) else 0
  · refine Finset.sum_congr rfl fun x _=>?_
    rw [map_prod]
    have reads (v : Old F⊕Link F) :
        reduce p f 1 ((file F cubic f p σ v).frozen hf (assignment N x v)) =
            if truth F cubic σ v (assignment N x v) then 1 else 0 :=
      CreatedEntry.read_created (file F cubic f p σ v) hf (assignment N x v)
    simp_rw [reads]
    by_cases h : Accept F cubic σ x
    · rw [if_pos h]
      simp only [show ∀v, truth F cubic σ v (assignment N x v)=true from h,
        if_true,Finset.prod_const_one]
    · rw [if_neg h]
      obtain ⟨v,hv⟩ : ∃v,truth F cubic σ v (assignment N x v)=false := by
        simpa only [Accept,not_forall,Bool.not_eq_true] using h
      apply Finset.prod_eq_zero (i:=v) (Finset.mem_univ v)
      simp [hv]
  · simp_rw [same_original_assignment F cubic]
    by_cases h : PinnedCNF.AllEdges F σ <;> simp [h]

#print axioms truth
#print axioms file_creation
#print axioms pin_file_local
#print axioms nonpin_file_unchanged
#print axioms read_subdivision
#print axioms read_tree_port
#print axioms occurrence_reaches_bridge
#print axioms bridge_forced_by_pin
#print axioms all_wires_forced
#print axioms tree_owner_same_variable
#print axioms same_original_assignment
#print axioms literal_contraction_is_uncloned_count
end
end Paper5.HybridDUncloned
