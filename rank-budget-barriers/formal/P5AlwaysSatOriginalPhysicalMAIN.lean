import P5AlwaysSatOriginalPhysicalMAINBase
import P5AlwaysSatOriginalPhysicalMAINNumbers
import P5AlwaysSatOriginalPhysicalSparsePorts

/-! The genuine direct and sparse MAIN source charts on the same cloned
(M.7) CNF. We instantiate the printed alphabet/mesh with n equal to the
actual number of copies, and transfer cell caps to the actual unary pins. -/
namespace Paper5.AlwaysSatOriginal.Physical
open scoped BigOperators Classical
open P5MainBalance P5MainIterator Filter
open J1MainSourcePlacement J1MainSourceCollision
open DiagonalAbundance (Draw)
open EmpiricalCutMoments

universe u

section Chart
variable {V P W F I S : Type*} [Fintype V] [Nonempty V] [Fintype P] [Fintype W] [Fintype F]
  [Fintype I] [Fintype S] [LinearOrder S]

/-- The ambient data are physical variable/factor words with a source
copy array. The selected sign cuts are unions of the actual factor symbols. -/
structure MAINCertificate (o : P→W) (f : P→F) (pin : V↪P) where
  data : IncidenceData I S P W F
  literal_owner : data.var=o
  literal_factor : data.factor=f
  owner_surj : Function.Surjective data.var
  cell_cap : ∀ u,load data.cell u≤2*(Fintype.card P:ℚ)/Fintype.card (Draw I S)
  variable_cap : ∀ i g,load (fun v : W=>data.wordVar v i) g≤2*(Fintype.card W:ℚ)/Fintype.card S
  copy_cap : (J1MainSourceBridge.copies data:ℚ)≤2*(Fintype.card P:ℚ)/Fintype.card (Draw I S)
  symbols : I→Finset S
  marked_balanced : ∀ i,
    (1/4:ℚ)*Fintype.card V ≤
      (min (BalancedUnion.vertexUnion (fun v=>data.wordFactor (f (pin v)) i) (symbols i)).card
        (Fintype.card V-(BalancedUnion.vertexUnion (fun v=>data.wordFactor (f (pin v)) i) (symbols i)).card):ℕ)

noncomputable def MAINCertificate.layout {o : P→W} {f : P→F} {pin : V↪P}
    (C : MAINCertificate (I:=I) (S:=S) o f pin) :
    SourceLayout P W F (Fin (J1MainSourceBridge.copies C.data)) I S :=
  MAINlayout C.data C.owner_surj

omit [Fintype F] [Nonempty V] in
theorem MAINCertificate.marked_word_at_seat {o : P→W} {f : P→F} {pin : V↪P}
    (C : MAINCertificate (I:=I) (S:=S) o f pin) (v : V) (i : I) :
    ((C.layout.placement.slot (pin v)).2 i).2=C.data.wordFactor (f (pin v)) i := by
  change C.data.wordFactor (C.data.factor (pin v)) i=C.data.wordFactor (f (pin v)) i
  exact congrArg (fun a=>C.data.wordFactor a i) (congrFun C.literal_factor (pin v))

omit [Fintype F] [Nonempty V] in
theorem MAINCertificate.physical_read {o : P→W} {f : P→F} {pin : V↪P}
    (C : MAINCertificate (I:=I) (S:=S) o f pin) (e : P) :
    occupied C.data (J1MainSourceBridge.copies C.data) (J1MainSourceBridge.copies_suffice C.data)
      (copyIndex C.data (J1MainSourceBridge.copies C.data) (J1MainSourceBridge.copies_suffice C.data) e)
      (C.data.cell e)=some (o e) := by
  exact (occupied_at C.data _ _ e).trans (congrArg some (congrFun C.literal_owner e))

variable [Nonempty P] [Nonempty W] [Nonempty I] [Nonempty S]

theorem actual_main_certificate (o : P→W) (f : P→F) (pin : V↪P)
    (surj : Function.Surjective o)
    (b w : ℕ) (hbow : 0<b+w)
    (hv : ∀ v : W,Nat.card {e : P // o e=v}≤b)
    (hf : ∀ g : F,Nat.card {e : P // f e=g}≤w)
    (hcell : 2*((b+w:ℕ):ℚ)*(Fintype.card (Draw I S):ℚ)^2≤Fintype.card P)
    (hgrp : 2*(Fintype.card I:ℚ)*(Fintype.card S:ℚ)^2≤Fintype.card W)
    (hP : 2*Fintype.card P≤54*Fintype.card V) (hR : 72≤Fintype.card S) :
    Nonempty (MAINCertificate (I:=I) (S:=S) o f pin) := by
  let j : I := Classical.choice inferInstance
  obtain ⟨cfg,hC,hV⟩ := actual_MAIN_labels (S:=S) j o f b w hbow hv hf hcell hgrp
  let D := mainData j o f cfg
  have hdom : ∀ x,empiricalLaw (fun v=>D.wordFactor (f (pin v))) x≤
      (54:ℚ)*ProductVariance.uniformWeight (I→S) :=
    Paper5.HybridClosure.main_pin_domination pin D.cell 54 hP hC
  have hR' : (72:ℚ)≤Fintype.card S := by exact_mod_cast hR
  have hslack : (54:ℚ)/(Fintype.card S:ℚ)≤3/4 := by
    apply (div_le_iff₀ (by linarith only [hR'])).2
    linarith only [hR']
  have hz (i : I) := BalancedUnion.exists_balanced_vertex_union_of_law
    (fun v=>D.wordFactor (f (pin v)) i) (fun a=>
      (Paper5.HybridClosure.marginal_domination (fun v=>D.wordFactor (f (pin v))) 54 hdom i a).trans hslack)
  choose U hU using hz
  exact ⟨⟨D,rfl,rfl,surj,hC,hV,MAIN_exact_copies D _ hC,U,hU⟩⟩
end Chart

section BothRoutes
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable (E : Finset (V×V)) (T : Finset V)

abbrev ActualI := Fin (mainNodes (Fintype.card (Port E T)))
abbrev ActualS := Fin (mainAlphabet (Fintype.card (Port E T)))

omit [DecidableEq V] [Nonempty V] in
theorem actual_main_dimensions [DecidableEq (ActualI E T)] :
    Fintype.card (Draw (ActualI E T) (ActualS E T))=mainCells (Fintype.card (Port E T)) := by
  unfold Draw mainCells ActualI ActualS
  simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,←pow_add,Nat.two_mul]

omit [DecidableEq V] [Nonempty V] in
theorem main_port_card_lower :
    Fintype.card V≤Fintype.card (Port E T) ∧
      Fintype.card (Port E T)≤Fintype.card (ClausePort E T) ∧
      Fintype.card (Port E T)≤Fintype.card (SparsePort E T) := by
  have h₁ := original_port_card E T
  have h₂ := port_card E T
  have h₃ : Fintype.card (SparsePort E T)=Fintype.card (ClausePort E T)+Fintype.card (Port E T) :=
    Fintype.card_sum
  omega

omit [Nonempty V] in
theorem main_and_sparse_port_caps (hC : ∀ v,GraphCutMoments.degree E v=3)
    (hT : T.card≤Fintype.card V/4) (hN : 8≤Fintype.card V) :
    2*Fintype.card (ClausePort E T)≤54*Fintype.card V ∧
      2*Fintype.card (SparsePort E T)≤54*Fintype.card V := by
  have hc := (original_physical_sizes E T (fun _=>false) hC).2.1
  have hs := sparse_port_count E T hC
  omega

set_option maxHeartbeats 5000000 in
theorem actual_main_and_sparse [Nonempty (ActualI E T)] [Nonempty (ActualS E T)]
    (hC : ∀ v,GraphCutMoments.degree E v=3)
    (hT : T.card≤Fintype.card V/4) (hN : 8≤Fintype.card V)
    (hR : 72≤mainAlphabet (Fintype.card (Port E T)))
    (hCell : 16*(mainCells (Fintype.card (Port E T)))^2≤Fintype.card (Port E T))
    (hGroup : 2*mainNodes (Fintype.card (Port E T))*(mainAlphabet (Fintype.card (Port E T)))^2≤
      Fintype.card (Port E T)) :
    Nonempty (MAINCertificate (I:=ActualI E T) (S:=ActualS E T)
      (portOwner E T) (portFactor E T) (marked E T)) ∧
    Nonempty (MAINCertificate (I:=ActualI E T) (S:=ActualS E T)
      (sparseOwner E T) (sparseFactor E T) (sparseMarked E T)) := by
  letI : DecidableEq (ActualI E T) := Classical.decEq _
  letI : Nonempty (Port E T) := ⟨bonusZeroPort E T⟩
  letI : Nonempty (ClausePort E T) := ⟨.inl (bonusZeroPort E T)⟩
  letI : Nonempty (SparsePort E T) := ⟨.inr (bonusZeroPort E T)⟩
  have hp := main_and_sparse_port_caps E T hC hT hN
  have hn := main_port_card_lower E T
  have hcellD : 2*((3+3:ℕ):ℚ)*(Fintype.card (Draw (ActualI E T) (ActualS E T)):ℚ)^2≤
      Fintype.card (ClausePort E T) := by
    rw [actual_main_dimensions E T]
    have he : 2*(3+3:ℕ)*(mainCells (Fintype.card (Port E T)))^2≤Fintype.card (ClausePort E T) :=
      (Nat.mul_le_mul_right _ (by decide : 2*(3+3:ℕ)≤16)).trans (hCell.trans hn.2.1)
    exact_mod_cast he
  have hcellS : 2*((4+3:ℕ):ℚ)*(Fintype.card (Draw (ActualI E T) (ActualS E T)):ℚ)^2≤
      Fintype.card (SparsePort E T) := by
    rw [actual_main_dimensions E T]
    have he : 2*(4+3:ℕ)*(mainCells (Fintype.card (Port E T)))^2≤Fintype.card (SparsePort E T) :=
      (Nat.mul_le_mul_right _ (by decide : 2*(4+3:ℕ)≤16)).trans (hCell.trans hn.2.2)
    exact_mod_cast he
  have hgrp : 2*(Fintype.card (ActualI E T):ℚ)*(Fintype.card (ActualS E T):ℚ)^2≤
      Fintype.card (Port E T) := by
    simpa only [ActualI,ActualS,Fintype.card_fin] using (by exact_mod_cast hGroup :
      (2:ℚ)*mainNodes (Fintype.card (Port E T))*(mainAlphabet (Fintype.card (Port E T)):ℚ)^2≤
        Fintype.card (Port E T))
  have hR' : 72≤Fintype.card (ActualS E T) := by simpa only [ActualS,Fintype.card_fin] using hR
  constructor
  · exact actual_main_certificate (I:=ActualI E T) (S:=ActualS E T)
      (portOwner E T) (portFactor E T) (marked E T) (port_owner_surjective E T) 3 3 (by decide)
      (physical_copy_degree_le E T) (fun f=>(factor_fibre_degree E T f).2)
      hcellD hgrp hp.1 hR'
  · exact actual_main_certificate (I:=ActualI E T) (S:=ActualS E T)
      (sparseOwner E T) (sparseFactor E T) (sparseMarked E T) (sparse_owner_surj E T) 4 3 (by decide)
      (sparse_copy_degree_le E T) (fun f=>(sparse_factor_degree E T f).2)
      hcellS hgrp hp.2 hR'

set_option maxHeartbeats 5000000 in
theorem uniform_main_and_sparse :
    ∃ N0 : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W] [Nonempty W]
      (E : Finset (W×W)) (T : Finset W),
      N0≤Fintype.card W → (∀ v,GraphCutMoments.degree E v=3) → T.card≤Fintype.card W/4 →
      Nonempty (MAINCertificate (I:=ActualI E T) (S:=ActualS E T)
        (portOwner E T) (portFactor E T) (marked E T)) ∧
      Nonempty (MAINCertificate (I:=ActualI E T) (S:=ActualS E T)
        (sparseOwner E T) (sparseFactor E T) (sparseMarked E T)) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp main_mesh_eventual
  refine ⟨max 8 N,?_⟩
  intro W _ _ _ A B hn hC hB
  have hsize : N≤Fintype.card (Port A B) :=
    ((le_max_right 8 N).trans hn).trans (main_port_card_lower A B).1
  obtain ⟨hR,hQ,hcell,hgrp⟩ := hN _ hsize
  letI : Nonempty (ActualI A B) := ⟨⟨0,hQ⟩⟩
  letI : Nonempty (ActualS A B) := ⟨⟨0,(by decide : 0<(72:ℕ)).trans_le hR⟩⟩
  exact actual_main_and_sparse A B hC hB ((le_max_left 8 N).trans hn) hR hcell hgrp
end BothRoutes

#print axioms MAINCertificate.marked_word_at_seat
#print axioms MAINCertificate.physical_read
#print axioms actual_main_certificate
#print axioms actual_main_dimensions
#print axioms main_port_card_lower
#print axioms main_and_sparse_port_caps
#print axioms actual_main_and_sparse
#print axioms uniform_main_and_sparse
end Paper5.AlwaysSatOriginal.Physical