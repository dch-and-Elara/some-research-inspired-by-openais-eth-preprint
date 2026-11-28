
import J2R43LiteralWholeMenuExec
import J1PhysicalHost

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
set_option maxSynthPendingDepth 16
set_option linter.unusedSectionVars false

/-! The v7 exterior tie on the very edge set already used by the J1
MAIN witnesses. No graph orientation or clone ports are transported. -/
namespace J2R43LiteralWholeMenu
open scoped Classical BigOperators
open Paper5.HybridClosure J1PhysicalHost J1MainSourceLabels J1MainSourceCollision
open DiagonalAbundance J6R10Repack J6R11CollisionReindex J6R11Collision P11FullPacking
noncomputable section
variable {B : Type} [Fintype B] [DecidableEq B]
variable (M : Match B)
local notation "F" => (edges M)
local notation "reg" => (degree_eq_three M)
local notation "N" => (dNetwork F reg)
local notation "V" => (Vertex B)
local notation "P0" => (MainClonedCNF.Port F)
local notation "W" => (DWire F)

def exteriorPairTag (p : Vertex B) : Vertex B :=
  if pick M p then p else M.mate p

theorem exterior_pair_tag_equal (p : Vertex B) :
    exteriorPairTag M (M.mate p)=exteriorPairTag M p := by
  by_cases h : pick M p
  · have h' : ¬pick M (M.mate p) := fun h' => (pick_mate_iff M p).1 h' h
    simpa [exteriorPairTag,h,h'] using M.inv p
  · have h' : pick M (M.mate p) := (pick_mate_iff M p).2 h
    simp [exteriorPairTag,h,h']

theorem exterior_pair_tag_members (p x : Vertex B) (h : exteriorPairTag M p=x) :
    p=x ∨ p=M.mate x := by
  unfold exteriorPairTag at h
  split at h
  · exact Or.inl h
  · exact Or.inr ((M.inv p).symm.trans (congrArg M.mate h))

def literalOldTie : DOld F→Option (Vertex B)
  | .inr (.inl p) => some (exteriorPairTag M p)
  | _ => none

def literalUnaryWire (p : Vertex B) : W := (.inl p,true)

theorem literal_unary_tied (p : Vertex B) :
    literalOldTie M ((N).row (literalUnaryWire M p))=some (exteriorPairTag M p) := rfl

theorem exactly_unary_wires_are_tied :
    (tiedSlots (literalOldTie M ∘ (N).row)).card=Fintype.card (Vertex B) := by
  let j : Vertex B↪W := ⟨literalUnaryWire M,fun _ _ h=>Sum.inl.inj (congrArg Prod.fst h)⟩
  have hj : tiedSlots (literalOldTie M ∘ (N).row)=Finset.univ.map j := by
    ext q
    obtain ⟨q,b⟩ := q
    cases b
    · simp [tiedSlots,literalOldTie,dNetwork,j,literalUnaryWire]
    · rcases q with q|q
      · simp [tiedSlots,literalOldTie,dNetwork,cloneFactor,j,literalUnaryWire]
      · rcases q with q|q <;> simp [tiedSlots,literalOldTie,dNetwork,cloneFactor,j,literalUnaryWire]
  rw [hj,Finset.card_map,Finset.card_univ]

theorem no_more_than_two_wires_per_exterior_tag (p : Vertex B) :
    (tagFibre (literalOldTie M ∘ (N).row) p).card≤2 := by
  have hs : tagFibre (literalOldTie M ∘ (N).row) p ⊆
      {literalUnaryWire M p,literalUnaryWire M (M.mate p)} := by
    intro e he
    have h := (Finset.mem_filter.mp he).2
    obtain ⟨w,b⟩ := e
    cases b
    · simp [literalOldTie,dNetwork] at h
    · rcases w with w|w
      · have h' : exteriorPairTag M w=p := Option.some.inj h
        rcases exterior_pair_tag_members M w p h' with hw|hw
        · subst w
          exact Finset.mem_insert_self _ _
        · subst w
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      · rcases w with w|w <;> simp [literalOldTie,dNetwork,cloneFactor] at h
  calc
    _ ≤ ({literalUnaryWire M p,literalUnaryWire M (M.mate p)}:Finset W).card := Finset.card_le_card hs
    _ ≤ ({literalUnaryWire M (M.mate p)}:Finset W).card+1 := Finset.card_insert_le _ _
    _ = 2 := by simp

abbrev SeedPrimitive (a : ℕ) := Primitive P0 (DOld F) (Vertex B) (Fin a)

def seedWords {a : ℕ} (i : Fin a) (z : SeedPrimitive M a→Fin 64) :
    Sample (DOld F) P0 (Fin a→Fin 64) :=
  (factorWord i (literalOldTie M) z,variableWord z)

theorem same_graph_expected_seed_phi {a : ℕ} (i : Fin a) :
    mean (fun z : SeedPrimitive M a→Fin 64 =>
      varianceScore (declaredCell N (seedWords M i z).1 (seedWords M i z).2)) ≤
      4*(Nat.card W:ℚ)+Fintype.card (Vertex B) := by
  let T := literalOldTie M
  have hcount := bad_pairs_with_ties T (N).col (N).row 2 3 1 (Fintype.card (Vertex B))
    (fun v=>by
      have hr := (d_subdivision_degree F reg v).le
      convert hr using 1
      congr 1
      ext q
      simp [varFibre]) (fun v=>by
      have hr := d_old_degree F reg v
      convert hr using 1
      congr 1
      ext q
      simp [facFibre])
    (no_more_than_two_wires_per_exterior_tag M) (exactly_unary_wires_are_tied M).le
  have hp := expected_incidenceCost (S:=Fin 64) i T (N).col (N).row
  have hp' : mean (incidenceCost (S:=Fin 64) i T (N).col (N).row)≤
      4*(Nat.card W:ℚ)+Fintype.card (Vertex B) := by
    apply hp.trans
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast (by simpa using hcount :
      (badPairs T (N).col (N).row).card≤4*Fintype.card W+Fintype.card (Vertex B))
  have hswap (z : SeedPrimitive M a→Fin 64) :
      varianceScore (declaredCell N (seedWords M i z).1 (seedWords M i z).2) =
      incidenceCost i T (N).col (N).row z := by
    have hg := declared_variance_eq N (seedWords M i z)
    have hrel := deviation_relabel (Equiv.prodComm (Fin a→Fin 64) (Fin a→Fin 64))
      (literalCell i T (N).col (N).row z)
    exact hg.trans hrel
  rw [funext hswap]
  exact hp'

theorem same_graph_tied_D_seed {a : ℕ} (i : Fin a) (Δ : ℕ) (hΔ : 3≤Δ)
    (hcollision : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card W)
    (hslots : 2^a*J9PrintedSchedule.arrayCard a≤Nat.card W) :
    ∃ z : SeedPrimitive M a→Fin 64, ∃ P : PhysicalPacking N a (Fin 64),
      (∀ p : Vertex B, P.rowLabel (.inr (.inl p)) i =
        z (.inr (.inr (exteriorPairTag M p)))) ∧
      P.copies=ceilCopies (2^a) (maxFiber (declaredCell N P.rowLabel P.colLabel)) ∧
      varianceScore (declaredCell N P.rowLabel P.colLabel)≤2*(Nat.card W:ℚ)*Δ := by
  obtain ⟨z,hz⟩ := mean_le_select (fun z : SeedPrimitive M a→Fin 64 =>
    varianceScore (declaredCell N (seedWords M i z).1 (seedWords M i z).2))
  have hp := hz.trans (same_graph_expected_seed_phi M i)
  have hm : (Nat.card W:ℚ)=24*(Fintype.card (Vertex B):ℚ) := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast d_physical_wire_count F reg
  have hp₁ : 4*(Nat.card W:ℚ)+Fintype.card (Vertex B)≤6*(Nat.card W:ℚ) := by
    rw [hm]
    linarith only [Nat.cast_nonneg (α:=ℚ) (Fintype.card (Vertex B))]
  have hp₂ : (6:ℚ)*(Nat.card W:ℚ)≤2*(Nat.card W:ℚ)*Δ := by
    have h : (3:ℚ)≤Δ := by exact_mod_cast hΔ
    have h' := mul_le_mul_of_nonneg_left h (show (0:ℚ)≤2*(Nat.card W:ℚ) by positivity)
    linarith only [h']
  obtain ⟨P,hrow,hcol,hcopy⟩ := actual_rounded_packing N (G:=Fin 64) (by simp)
    (seedWords M i z).1 (seedWords M i z).2 Δ (hp.trans (hp₁.trans hp₂)) hcollision hslots
  refine ⟨z,P,?_,?_,?_⟩
  · intro p
    rw [hrow]
    simp [seedWords,factorWord,factorKey,literalOldTie]
  · rw [hrow,hcol,hcopy]
  · rw [hrow,hcol]
    exact hp.trans (hp₁.trans hp₂)

#print axioms exterior_pair_tag_equal
#print axioms exterior_pair_tag_members
#print axioms literal_unary_tied
#print axioms exactly_unary_wires_are_tied
#print axioms no_more_than_two_wires_per_exterior_tag
#print axioms same_graph_expected_seed_phi
#print axioms same_graph_tied_D_seed
end
end J2R43LiteralWholeMenu
