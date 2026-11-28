import J1R43LiteralMoments
import J1R43LiteralDriver
import J1R43LiteralReserve
import J1PhysicalAccepted
import J1PPrintedMain
import J6R11CollisionGreedy

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2500000
set_option maxRecDepth 1800
set_option maxSynthPendingDepth 18
set_option linter.unusedSectionVars false

/-! The chooser evaluates the exact local conditional score on the real
printed four-clone MAIN incidences. The same selected primitive assignment
proves every source cap and every actual indexed source group count. -/
namespace J1R43Literal
open scoped BigOperators
open DiagonalAbundance J1MainSourceLabels J1MainSourceCollision J1MainSourceBridge
open J1MainSourcePlacement MainProbe MainClonedCNF J1PhysicalHost
open J1PhysicalIncidence J1PhysicalIndependent J1PhysicalCertificate J1PhysicalBounds
open GuardExpectation (average)
noncomputable section

variable {B I S : Type*} [Fintype B] [DecidableEq B]
  [Fintype I] [DecidableEq I] [Nonempty I] [Fintype S] [DecidableEq S] [Nonempty S]

/-- Match the structural instances of the literal vertex/factor/port types.
These are executable equality tests on stored graph labels. -/
scoped instance literalFactorEq (E : Finset (Vertex B × Vertex B)) : DecidableEq (Factor E) :=
  @instDecidableEqSum (Vertex B) (↥E ⊕ Variable (Vertex B)) inferInstance
    (@instDecidableEqSum (↥E) (Variable (Vertex B)) inferInstance inferInstance)

scoped instance literalPortEq (E : Finset (Vertex B × Vertex B)) : DecidableEq (Port E) :=
  @instDecidableEqSum (Vertex B) ((↥E × Bool) ⊕ (Vertex B × Fin 4 × Bool)) inferInstance
    (@instDecidableEqSum (↥E × Bool) (Vertex B × Fin 4 × Bool) inferInstance inferInstance)

scoped instance literalKeyEq (M : Match B) : DecidableEq (ConfigKey M I) :=
  @instDecidableEqSum (Variable (Vertex B)×I) ((Factor (edges M)×I)⊕B)
    inferInstance (@instDecidableEqSum (Factor (edges M)×I) B inferInstance inferInstance)

local notation "N" => Fintype.card (Vertex B)
local notation "Q" => Fintype.card I
local notation "r" => Fintype.card S

def originalPrintedScore (M : Match B) (t : I) (H : Finset (Vertex B))
    (z : ConfigKey M I → S) : ℚ :=
  printedScore t (tie (edges M) Prod.fst) (portVar (edges M) (degree_eq_three M))
    (portFactor (edges M)) (pinSubset M H) (sourceMu H I S) z

def compactOriginal (M : Match B) (t : I) (H : Finset (Vertex B))
    (w : Marginals (ConfigKey M I) S) : ℚ :=
  localScore t (tie (edges M) Prod.fst) (portVar (edges M) (degree_eq_three M))
    (portFactor (edges M)) (pinSubset M H) (sourceMu H I S) w

def selected (M : Match B) (t : I) (H : Finset (Vertex B))
    (keys : List (ConfigKey M I)) (palette : List S) (default : S) :
    (ConfigKey M I → S) × ℕ :=
  chooseLayout (compactOriginal M t H) palette default keys (fun _ _ => (r:ℚ)⁻¹)

theorem physical_uniform_score (M : Match B) (t : I) (H : Finset (Vertex B))
    (hI : Independent M H) (hsize : 48*Q*r^2*r^Q<H.card) :
    mean (originalPrintedScore M t H (S:=S))<2 := by
  have hpos : 0<H.card := by omega
  letI : Nonempty H := ⟨⟨_,Classical.choose_spec (Finset.card_pos.mp hpos)⟩⟩
  have hN : 0<N := hpos.trans_le (Finset.card_le_univ H)
  let pvar : H ↪ Variable (Vertex B) :=
    ⟨fun v => (v.val,0),fun _ _ h => Subtype.ext (congrArg Prod.fst h)⟩
  let pfac : H ↪ Factor (edges M) :=
    ⟨fun v => Sum.inl v.val,fun _ _ h => Subtype.ext (Sum.inl_injective h)⟩
  let block : Variable (Vertex B) → B := fun v => v.1.1
  have hv (a : H) : portVar (edges M) (degree_eq_three M) (pinSubset M H a) = pvar a := rfl
  have hf (a : H) : portFactor (edges M) (pinSubset M H a) = pfac a := rfl
  have ht (a : H) : tie (edges M) Prod.fst (pfac a) = some (block (pvar a)) := rfl
  have hind : ∀ a a' : H, ¬triangleEdge block (pvar a) (pvar a') := by
    intro a a' h
    exact triangle_restriction M H hI a a' ⟨fun hv' => h.1 (Prod.ext hv' rfl),h.2⟩
  have hM := port_card (edges M) (degree_eq_three M)
  have hn := variables_card (V:=Vertex B)
  have hΦ := expected_main_phi (S:=S) t (tie (edges M) Prod.fst)
    (portVar (edges M) (degree_eq_three M)) (portFactor (edges M)) N
    (var_degree_bound (edges M) (degree_eq_three M))
    (by
      intro e
      convert factor_scope_bound (edges M) e using 1)
    (tag_degree_bound (edges M) Prod.fst (fun b => le_of_eq (block_card b)))
    (le_of_eq (number_tied_slots (edges M) Prod.fst))
  have hΞ := expected_variableCost (V:=Variable (Vertex B)) (F:=Factor (edges M)) (B:=B) (I:=I) (S:=S)
  rw [hM,Nat.cast_mul,Nat.cast_ofNat] at hΦ
  rw [hn,Nat.cast_mul,Nat.cast_ofNat] at hΞ
  have hsize' : 48*Q*r^2*r^Q<Fintype.card H := by rwa [Fintype.card_coe]
  exact actual_joint_uniform_mean t (tie (edges M) Prod.fst) (portVar (edges M) (degree_eq_three M))
    (portFactor (edges M)) (pinSubset M H) pvar pfac pvar block
    hv hf ht hind N hN hM hn hΦ hΞ hsize'

theorem selected_score_lt (M : Match B) (t : I) (H : Finset (Vertex B))
    (hI : Independent M H) (hsize : 48*Q*r^2*r^Q<H.card)
    (keys : List (ConfigKey M I)) (keyNodup : keys.Nodup) (keyAll : ∀ k, k ∈ keys)
    (palette : List S) (all : ∀ g, g ∈ palette) (default : S) :
    originalPrintedScore M t H (selected M t H keys palette default).1<2 := by
  let w : Marginals (ConfigKey M I) S := fun _ _ => (r:ℚ)⁻¹
  have h0 : ∀ i a, 0≤w i a := by intro i a; unfold w; positivity
  have h1 (i : ConfigKey M I) : ∑ a, w i a=1 := by
    simp [w,nsmul_eq_mul]
  have hstep : originalPrintedScore M t H (selected M t H keys palette default).1 ≤
      average w (originalPrintedScore M t H) := by
    unfold selected
    exact chooseLayout_correct (compactOriginal M t H) palette default all
      (originalPrintedScore M t H) (fun a ha => (exact_conditional_printed_score t
        (tie (edges M) Prod.fst) (portVar (edges M) (degree_eq_three M)) (portFactor (edges M))
        (pinSubset M H) (sourceMu H I S) a ha).symm)
      keys keyNodup keyAll w h0 h1
  rw [show average w (originalPrintedScore M t H)=mean (originalPrintedScore M t H) from
      J6R11CollisionGreedy.uniform_product_mean _] at hstep
  exact hstep.trans_lt (physical_uniform_score M t H hI hsize)

theorem original_caps_and_hits_of_score (M : Match B) (t : I) (H : Finset (Vertex B))
    (hh : 0<H.card) (cfg : ConfigKey M I → S)
    (hm : (10:ℚ)*(Fintype.card (Draw I S):ℚ)^2≤(Fintype.card (Port (edges M)):ℚ))
    (hn : (2:ℚ)*(Q:ℚ)*(r:ℚ)^2≤(Fintype.card (Variable (Vertex B)):ℚ))
    (hs : originalPrintedScore M t H cfg<2) :
    (∀ c, load ((physicalData M t cfg).cell) c <
      2*((Fintype.card (Port (edges M)):ℚ)/(Fintype.card (Draw I S):ℚ))) ∧
    (∀ i g, load (fun v : Variable (Vertex B) => variableWord cfg v i) g <
      2*((Fintype.card (Variable (Vertex B)):ℚ)/(r:ℚ))) ∧
    (∀ i g, sourceMu H I S / 2 <
      ((ownedPins (compiledLayout (physicalData M t cfg) (pinSubset M H)) i g Finset.univ).card:ℚ)) := by
  letI : Nonempty H := ⟨⟨_,Classical.choose_spec (Finset.card_pos.mp hh)⟩⟩
  let cost (z : ConfigKey M I → S) : ℚ :=
    physicalPhi M t z/(5*(Fintype.card (Port (edges M)):ℚ))+
      physicalXi M z/((Q:ℚ)*(Fintype.card (Variable (Vertex B)):ℚ))
  have h0 : 0≤cost cfg := by
    unfold cost physicalPhi physicalXi
    exact add_nonneg (div_nonneg (deviation_nonneg _) (by positivity))
      (div_nonneg (Finset.sum_nonneg (fun _ _ => deviation_nonneg _)) (by positivity))
  have hN : 0<N := hh.trans_le (Finset.card_le_univ H)
  change jointScore cost _ _ cfg < 2 at hs
  obtain ⟨hcost,hpins⟩ := pointwise_certificate cost _ (sourceMu H I S) sourceMu_pos h0 hs
  have hcost' : physicalPhi M t cfg / (5*(12*(N:ℚ))) +
      physicalXi M cfg / ((Q:ℚ)*(4*(N:ℚ)))<2 := by
    simpa only [cost,port_card (edges M) (degree_eq_three M),variables_card,Nat.cast_mul,
      Nat.cast_ofNat] using hcost
  obtain ⟨hcell,hgroup⟩ := original_caps M t cfg hN hm hn hcost'
  refine ⟨hcell,hgroup,?_⟩
  intro i g
  have ha := hpins (i,g)
  change _ < hitCount i g ((physicalData M t cfg).cell ∘ pinSubset M H) at ha
  rw [hitCount_is_actual_card] at ha
  change _ < ((ownedPins (enumerateLayout _ _ _ _) i g Finset.univ).card:ℚ)
  rwa [owned_card_hits]

theorem conditioned_graph_layout (M : Match B) (b : B) (special : I)
    (vertices : List (Vertex B)) (allVertices : ∀ v, v ∈ vertices)
    (keys : List (ConfigKey M I)) (keyNodup : keys.Nodup) (allKeys : ∀ k, k ∈ keys)
    (palette : List S) (allSymbols : ∀ g, g ∈ palette) (default : S)
    (size : 192*Q*r^2*r^Q+6<N)
    (hcell : 10*(r^(2*Q))^2≤12*N) (hgroup : 2*Q*r^2≤4*N) :
    let H := reserveRun M b vertices ∅
    let cfg := selected M special H keys palette default
    H ⊆ available M b ∧ Independent M H ∧ N≤4*H.card+6 ∧
    originalPrintedScore M special H cfg.1<2 ∧
    (∀ c, load ((physicalData M special cfg.1).cell) c <
      2*((Fintype.card (Port (edges M)):ℚ)/(Fintype.card (Draw I S):ℚ))) ∧
    (∀ i g, load (fun v : Variable (Vertex B) => variableWord cfg.1 v i) g <
      2*((Fintype.card (Variable (Vertex B)):ℚ)/(r:ℚ))) ∧
    (∀ i g, sourceMu H I S / 2 <
      ((ownedPins (compiledLayout (physicalData M special cfg.1) (pinSubset M H)) i g Finset.univ).card:ℚ)) ∧
    cfg.2 = 2*keys.length*palette.length := by
  let H := reserveRun M b vertices ∅
  obtain ⟨hh,hi,hN⟩ := graph_only_reserve M b vertices allVertices
  change N≤4*H.card+6 at hN
  have hs' : 48*Q*r^2*r^Q<H.card := by
    have hmul : 192*Q*r^2*r^Q=4*(48*Q*r^2*r^Q) := by ring
    rw [hmul] at size
    omega
  have h0 : 0<H.card := by omega
  have hS := selected_score_lt M special H hi hs' keys keyNodup allKeys palette allSymbols default
  have hC : (10:ℚ)*(Fintype.card (Draw I S):ℚ)^2≤(Fintype.card (Port (edges M)):ℚ) := by
    rw [J1PhysicalAccepted.cell_count,port_card (edges M) (degree_eq_three M)]
    exact_mod_cast hcell
  have hG : (2:ℚ)*(Q:ℚ)*(r:ℚ)^2≤(Fintype.card (Variable (Vertex B)):ℚ) := by
    rw [variables_card]
    exact_mod_cast hgroup
  obtain ⟨hc,hg,hits⟩ := original_caps_and_hits_of_score M special H h0 _ hC hG hS
  refine ⟨hh,hi,hN,hS,hc,hg,hits,?_⟩
  unfold selected
  exact chooseLayout_calls (compactOriginal M special H) palette default keys (fun _ _=>(r:ℚ)⁻¹)

#print axioms physical_uniform_score
#print axioms selected_score_lt
#print axioms original_caps_and_hits_of_score
#print axioms conditioned_graph_layout

end
end J1R43Literal