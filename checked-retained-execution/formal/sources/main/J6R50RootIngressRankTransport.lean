import J6R50RootIngressRankChart

/-! Independent explicit half-wire and subdivision choices produce
a lawful Plant on the same literal gate network. Comparison to the
preserved choice is a pair of permutations, not a byte equality. -/
namespace J6R50RootIngress
open scoped Classical
open Std.Sat J7R10Plant J7R10Ports J7R10Counts J7R9Subdivision
open J6OrientedHost J6OrientedHostEval J6RecursivePortCube
open J6R49RootIngress
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6200000

variable {V : Type} [DecidableEq V] [Fintype V] (H : CNF V)
abbrev HalfRanks := Half H ≃ Fin (nWires H)
abbrev SubdivRanks := J7R9Compiler.Wire H ≃ Fin (nSubdiv H)

noncomputable def rankedPlant (W : HalfRanks H) (S : SubdivRanks H) :
    Plant (Old H) (nWires H) (nSubdiv H) where
  degree := J7R10Ports.degree H
  old := gate H
  rowPort := (rowChart H).trans W
  colPort := (Equiv.prodCongr S.symm (Equiv.refl Bool)).trans W

theorem original_plant_ranked :
    rankedPlant H (wireNumber H) (subdivNumber H)=physicalPlant H := rfl

def ranksReindex {A B : Type*} (left right : A≃B) : B≃B := left.symm.trans right

theorem row_rank_transport (W₁ W₂ : HalfRanks H) (S₁ S₂ : SubdivRanks H)
    (p : OldPort H) :
    ranksReindex W₁ W₂ ((rankedPlant H W₁ S₁).rowPort p)=
      (rankedPlant H W₂ S₂).rowPort p := by
  simp [ranksReindex,rankedPlant]

theorem col_rank_transport (W₁ W₂ : HalfRanks H) (S₁ S₂ : SubdivRanks H)
    (j : Fin (nSubdiv H)) (b : Bool) :
    ranksReindex W₁ W₂ ((rankedPlant H W₁ S₁).colPort (j,b))=
      (rankedPlant H W₂ S₂).colPort (ranksReindex S₁ S₂ j,b) := by
  simp [ranksReindex,rankedPlant]

theorem coreA_rank_transport (W₁ W₂ : HalfRanks H) (S₁ S₂ : SubdivRanks H)
    (x : Fin (nWires H)→Bool) :
    coreA (rankedPlant H W₁ S₁) (x ∘ ranksReindex W₁ W₂)=
      coreA (rankedPlant H W₂ S₂) x := by
  unfold coreA
  congr 1
  funext v
  change (gate H v).eval (fun j => x (ranksReindex W₁ W₂ ((rankedPlant H W₁ S₁).rowPort ⟨v,j⟩))) =
    (gate H v).eval (fun j => x ((rankedPlant H W₂ S₂).rowPort ⟨v,j⟩))
  apply congrArg (gate H v).eval
  funext j
  rw [row_rank_transport H W₁ W₂ S₁ S₂ ⟨v,j⟩]

theorem coreB_rank_transport (W₁ W₂ : HalfRanks H) (S₁ S₂ : SubdivRanks H)
    (x : Fin (nWires H)→Bool) :
    coreB (rankedPlant H W₁ S₁) (x ∘ ranksReindex W₁ W₂)=
      coreB (rankedPlant H W₂ S₂) x := by
  unfold coreB good
  simp only [Function.comp_apply,decide_eq_true_eq]
  apply Bool.decide_congr
  constructor
  · intro all j
    obtain ⟨k,rfl⟩ := (ranksReindex S₁ S₂).surjective j
    simpa only [col_rank_transport H W₁ W₂ S₁ S₂] using all k
  · intro all k
    rw [col_rank_transport H W₁ W₂ S₁ S₂ k false,col_rank_transport H W₁ W₂ S₁ S₂ k true]
    exact all (ranksReindex S₁ S₂ k)

theorem chart_sensitive_column_payload (W₁ W₂ : HalfRanks H) (S : SubdivRanks H) {c : ℕ}
    (fit : nSubdiv H≤2^c)
    (same : ∀ u : Fin (nWires H),
      let p := (rankedPlant H W₁ S).colPort.symm u
      let q := (rankedPlant H W₂ S).colPort.symm u
      (wordAt c p.1.val,p.2)=(wordAt c q.1.val,q.2)) :
    W₁=W₂ := by
  have inv : (rankedPlant H W₁ S).colPort.symm=(rankedPlant H W₂ S).colPort.symm := by
    apply Equiv.ext
    intro u
    let p := (rankedPlant H W₁ S).colPort.symm u
    let q := (rankedPlant H W₂ S).colPort.symm u
    have j : p.1.val=q.1.val :=
      wordAt_rank_inj (p.1.isLt.trans_le fit) (q.1.isLt.trans_le fit) (congrArg Prod.fst (same u))
    have b : p.2=q.2 := congrArg (fun z : A1R10.Word c×Bool => z.2) (same u)
    exact Prod.ext (Fin.ext j) b
  have e : (rankedPlant H W₁ S).colPort=(rankedPlant H W₂ S).colPort := by
    simpa only [Equiv.symm_symm] using congrArg (fun e : Fin (nWires H) ≃ Fin (nSubdiv H)×Bool => e.symm) inv
  apply Equiv.ext
  intro p
  have x := congrArg (fun K : Fin (nSubdiv H)×Bool≃Fin (nWires H) => K (S p.1,p.2)) e
  simpa [rankedPlant] using x

/-- A nonempty source wire admits two numerically different lawful
half rankings without changing the formula or the structural table
semantics. This does not assert that the finite old ranks are
noncomputable when their choices are exported. -/
theorem raw_chart_not_fixed_by_gate_syntax (W : HalfRanks H) (S : SubdivRanks H)
    (v : J7R9Compiler.Wire H) {c : ℕ} (fit : nSubdiv H≤2^c) :
    ∃ W' : HalfRanks H, W'≠W ∧ ∃ u : Fin (nWires H),
      let p := (rankedPlant H W' S).colPort.symm u
      let q := (rankedPlant H W S).colPort.symm u
      (wordAt c p.1.val,p.2)≠(wordAt c q.1.val,q.2) := by
  let flip : Half H≃Half H := Equiv.prodCongr (Equiv.refl _) (Equiv.swap false true)
  let W' : HalfRanks H := flip.trans W
  have distinct : W'≠W := by
    intro h
    have hh := congrArg (fun f : HalfRanks H => f (v,false)) h
    have vxy : W (v,true)=W (v,false) := by
      simp [W',flip] at hh
    have vv := congrArg Prod.snd (W.injective vxy)
    cases vv
  refine ⟨W',distinct,?_⟩
  by_contra! hx
  exact distinct (chart_sensitive_column_payload H W' W S fit (fun u => not_not.mp (hx u)))

#print axioms original_plant_ranked
#print axioms row_rank_transport
#print axioms col_rank_transport
#print axioms coreA_rank_transport
#print axioms coreB_rank_transport
#print axioms chart_sensitive_column_payload
#print axioms raw_chart_not_fixed_by_gate_syntax
end J6R50RootIngress
