import P5HybridClosurePrintedGrowth

/-! Final finite certificate at the literal printed root parameters.
The separate eventually theorem is uniform in graph-only base choices. -/
namespace Paper5.HybridClosure.Printed
open scoped Topology BigOperators Classical
open Filter J6R10Repack GroupProducts SeparatedRank EmpiricalCutMoments
open DiagonalAbundance (Draw)

section Constructor
variable {V TM TD R S K : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype TM] [Fintype TD] [CommRing R] [CommRing S] [Nontrivial S] [Field K]
variable (E : Finset (V×V)) (cubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)
local notation "N" => Fintype.card (TriVertex V)
local notation "F" => replacedEdges E cubic
local notation "reg" => replaced_cubic E cubic loopless
local notation "Net" => dNetwork F reg

omit [DecidableEq V] [Nonempty V] in
theorem main_node_range (t : Fin (mainQ N)) :
    1≤t.val+1 ∧ t.val+1≤mainQ N := by omega

set_option maxHeartbeats 8000000 in
/-- The returned proposition is the full finite E1 conclusion, at Q,r,a,Δ
computed from the original printed n=4N and s=n+m. A theorem-valued
application keeps the full statement without a new summary predicate. -/
theorem checked_actual_printed_E1 (gamma : ℚ) (hg : 0<gamma) (hg₃ : gamma≤3)
    (expand : ∀ U : Finset V, gamma*(min U.card (Fintype.card V-U.card):ℕ)≤
      ((GraphCutMoments.boundary E U).card:ℚ))
    (ready : Ready gamma N) (t : Fin (mainQ N)) (i : retainedCoordinates N) :
    ∃ (z : MainPrimitives F (Fin (mainQ N))→Fin (mainR N)) (P : PhysicalPacking Net (dA N) (Fin 64))
      (cM : V→Fin (mainR N)) (cD : E→Fin 64),
      let L_M := MainPinLabels E cubic t z
      let L_D := DPinLabels E cubic loopless P (retainedCoordinates N)
      let dM := routeDepth (gamma/3) N (mainQ N)
      let dD := routeDepth (gamma/3) (Fintype.card (TriVertex V)) (retainedCoordinates N).card
      (∀p,L_M p t=mainPinColor cM p) ∧
      (∀p,L_D p i=dPinColor E cubic cD p) ∧
      MainSeatCertificate F reg t z (2*(12*(Fintype.card (TriVertex V):ℚ))/
        (Fintype.card (Draw (Fin (mainQ N)) (Fin (mainR N))):ℚ)) ∧
      (∃ (monoM : ∀e∈innerEdges V,L_M e.1 t=L_M e.2 t)
        (monoD : ∀e∈outerEdges E cubic,L_D e.1 i=L_D e.2 i),
        ∀σ,clonedCount E cubic loopless σ =
          (∏g : Fin (mainR N), groupOperand (innerEdges V) (fun p=>L_M p t) monoM g (σ ∘ Subtype.val))*
          (∏h : Fin 64,groupOperand (outerEdges E cubic) (fun p=>L_D p i) monoD h (σ ∘ Subtype.val))) ∧
      (∀σ,boolAsNat (twoMethodScan E cubic cM cD σ).1=clonedCount E cubic loopless σ ∧
        (twoMethodScan E cubic cM cD σ).2≤7*Fintype.card (TriVertex V)+65) ∧
      (∃ (sM : Fin (mainQ N)→Finset (Fin (mainR N))) (sD : (retainedCoordinates N)→Finset (Fin 64)) (mark orientation : F→Bool),
        let matching := MatchingThinning.matching F (replaced_loopless E cubic loopless) mark orientation
        (∀j,dM≤endpointImbalance matching.endpoint (labelCut L_M id sM j)) ∧
        (∀j,dD≤endpointImbalance matching.endpoint (labelCut L_D id sD j)) ∧
        ∀ (terms_M : TM→GroupTerm L_M K) (terms_D : TD→GroupTerm L_D K)
          (embed : R→+*K) (residue : R→+*S) (_hinj : Function.Injective embed)
          (output : (TriVertex V→Bool)→R),
        (∀σ,embed (output σ)=(∑t,(terms_M t).value σ)+∑t,(terms_D t).value σ) →
        (∀σ,residue (output σ)=(clonedCount E cubic loopless σ:S)) →
        ((1:ℚ)≤(Fintype.card TM:ℚ)/(2:ℚ)^dM+(Fintype.card TD:ℚ)/(2:ℚ)^dD) ∧
          2^(min dM dD)≤Fintype.card TM+Fintype.card TD) :=
  checked_finite_E1 (TM:=TM) (TD:=TD) (R:=R) (S:=S) (K:=K)
    E cubic loopless gamma hg hg₃ expand
    (mainQ N) (mainR N) (dA N) (dDelta N) t ready.mainAlphabet (retainedCoordinates N) i ready.dDegree
    (by
      change 2*5*(mainCells N)^2≤12*N
      exact (Nat.mul_le_mul_right _ (by decide : 2*5≤12)).trans
        (ready.mainLayout.trans (by omega)))
    ready.mainGroups
    (by
      rw [Nat.card_eq_fintype_card,d_physical_wire_count F (replaced_cubic E cubic loopless)]
      exact ready.dCollision)
    (by
      rw [Nat.card_eq_fintype_card,d_physical_wire_count F (replaced_cubic E cubic loopless)]
      exact ready.dSlot)
    (by rw [retained_card]; exact ready.unionBudget)
end Constructor

theorem original_size_family_eventual (nodes : ℕ→ℕ)
    (hsize : Tendsto nodes atTop atTop) (gamma : ℚ) (hg : 0<gamma) :
    ∀ᶠ j : ℕ in atTop, Ready gamma (nodes j) :=
  hsize.eventually (actual_printed_eventual_ready gamma hg)

def firstMainNode {gamma : ℚ} {N : ℕ} (r : Ready gamma N) : Fin (mainQ N) :=
  ⟨0,r.mainNodes⟩

def firstDCoordinate {gamma : ℚ} {N : ℕ} (r : Ready gamma N) : retainedCoordinates N :=
  ⟨retainedEmbed N ⟨0,r.dNodes⟩,Finset.mem_map.mpr ⟨⟨0,r.dNodes⟩,Finset.mem_univ _,rfl⟩⟩


/-- The pointwise asymptotic certificate yields the rounded integer
exponent in a conventional statement of the term bound. -/
noncomputable def printedExponent (gamma : ℚ) (N : ℕ) : ℕ :=
  ⌊(matchingCoeff (gamma/3):ℝ)/(4*Real.sqrt printedLogConst)*
    ((N:ℝ)/Real.sqrt (Real.log (N:ℝ)))⌋₊

theorem printed_exp_term_count {gamma : ℚ} {N nM nD : ℕ} (ready : Ready gamma N)
    (h : 2^(min (routeDepth (gamma/3) N (mainQ N)) (routeDepth (gamma/3) N (dU N)))≤nM+nD) :
    2^printedExponent gamma N≤nM+nD := by
  have hc := Nat.floor_mono ready.depth
  rw [Nat.floor_natCast] at hc
  exact (Nat.pow_le_pow_right (by decide) hc).trans h

theorem eventually_uniform_at_order_cutoff (gamma : ℚ) (hg : 0<gamma) :
    ∃ n₀ : ℕ, ∀ N≥n₀, Ready gamma N :=
  eventually_atTop.1 (actual_printed_eventual_ready gamma hg)

#print axioms printed_exp_term_count
#print axioms eventually_uniform_at_order_cutoff
#print axioms main_node_range
#print axioms checked_actual_printed_E1
#print axioms original_size_family_eventual
#print axioms firstMainNode
#print axioms firstDCoordinate
end Paper5.HybridClosure.Printed