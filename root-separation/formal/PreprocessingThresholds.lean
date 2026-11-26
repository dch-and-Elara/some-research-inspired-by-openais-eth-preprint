import PTWireTopology
import PTMainRoute
import PTEntryBridge
import PTPacking
import PTHermiteGuard

namespace RootSeparation.Preprocessing

open Entry S11 GraphCutMoments SourceDensity

/-- For every fixed k >= 2, the main article reaches its sparse hash
counter on the normalized formula after the first sparsification node. -/
theorem main_entry_eventual (k : ℕ) (hk : 2 ≤ k) :
    ∃ N0 : ℕ, ∀ (V : Type u) [Fintype V] [DecidableEq V] (E : Finset (V × V)),
      N0 ≤ Fintype.card V → Entry.Simple E → (∀ v, degree E v = 3) →
      ∀ σ : V → Bool, MainLeaf E σ k := by
  obtain ⟨N0,hN⟩ := main_size_threshold
  refine ⟨N0,?_⟩
  intro V _ _ E hsize hs reg σ
  exact main_sparse_leaf E hs reg σ hk (hN _ hsize).1 (hN _ hsize).2

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The quantitative dispatcher has no unbounded high-density sequence on
these inputs. For the sizes to which its stated sparsification applies,
the actual density test has already selected the clause network. -/
theorem dense_only_bounded (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (hd : ¬ useSparse (n (V := V)) (m E)) : n (V := V) ≤ 16 := by
  by_contra! hn
  exact hd (sparse_dispatch E reg hn)

/-- The lower and upper constant multiples implicit in u = Theta(lambda/2^d).
The division rounding is accounted for with the additional factor of two. -/
theorem retained_scale {s d M : ℕ} (checks : ActiveNumbers s d M) :
    (131072*2^d)*retained s d ≤ lambda s ∧ lambda s ≤ (262144*2^d)*retained s d := by
  let b := 131072*(2:ℕ)^d
  let u := retained s d
  have hb : 0 < b := by unfold b; positivity
  have hu : 0 < u := checks.retainedPos
  have hlt : lambda s < (u+1)*b := by
    simpa [u,retained,b,Nat.mul_comm b] using Nat.lt_mul_div_succ (lambda s) hb
  have h2 : u+1 ≤ 2*u := by omega
  refine ⟨Nat.mul_div_le _ _, hlt.le.trans ?_⟩
  calc
    _ ≤ (2*u)*b := Nat.mul_le_mul_right _ h2
    _ = _ := by change (2*u)*b = (262144*2^d)*u; unfold b; ring

def active_probe_embedding {s d M : ℕ} (checks : ActiveNumbers s d M) :
    Fin (probeCount M (packetLength s d)) ↪ BitVec (4*lambda s) :=
  ⟨binaryProbe _ _ checks.probeCapacity, binaryProbe_injective _ _ checks.probeCapacity⟩

theorem active_positive_precision {s d M p : ℕ} (checks : ActiveNumbers s d M) (t : ℤ) :
    p < precision p M (labelLength s d) (retained s d) (packetLength s d) t := by
  have hM : 0 < M := checks.retainedPos.trans_le checks.retainedLeWire
  have h := Nat.mul_pos (show 0 < 8*M by omega) (show 0 < labelLength s d + 1 by omega)
  unfold precision
  omega

#print axioms main_entry_eventual
#print axioms dense_only_bounded
#print axioms retained_scale
#print axioms active_probe_embedding
#print axioms active_positive_precision

#check @RootSeparation.Preprocessing.normalize_pinned
#check @RootSeparation.Preprocessing.builtM_eq
#check @RootSeparation.Preprocessing.main_entry_eventual
#check @RootSeparation.Preprocessing.sparse_entry_admissible
#check @RootSeparation.Preprocessing.sparse_trace_eventual
#check @RootSeparation.Preprocessing.cutoff_graph_example
#check @RootSeparation.Preprocessing.active_retained_rpow


/-- Continue the numerical and graph-degree induction with the actual
retained-port child topology at a chosen grouping coordinate. -/
theorem active_step {W X Y : Type*} [Fintype W] [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {s d M0 : ℕ} (hcut : depthLogCutoff ≤ lambda s) (hroot : M0 ≤ 3*s)
    (row : W → X) (col : W → Y) (hreach : ReachSize M0 d (Fintype.card W))
    (hactive : leafThreshold s < Fintype.card W)
    (hr : ∀ v, SourceDensity.fiberCount row v ≤ degreeEnvelope s)
    (hc : ∀ v, SourceDensity.fiberCount col v ≤ degreeEnvelope s) :
    let a := labelLength s d
    let L := packetLength s d
    let cell := cellAt row col (selectedLabels row col (fun _ : Fin a => (0 : Fin 64)))
    let P := S8.Packet (Fin a) (Fin 64) (exactPad cell)
    ∃ G : Packing W P a L, G.cell = cell ∧ CollisionCertificate G.cell (degreeEnvelope s : ℚ) ∧
      ∀ (j : Fin a) (g : Fin 64),
        let M' := Fintype.card (GroupWires G.cell j g)
        ReachSize M0 (d+1) M' ∧
        (∀ v, SourceDensity.fiberCount (childOld G.cell j g row col) v ≤ degreeEnvelope s) ∧
        (∀ v, SourceDensity.fiberCount (childPacket G j g) v ≤ degreeEnvelope s) ∧
        (leafThreshold s < M' → ActiveNumbers s (d+1) M') := by
  classical
  intro a L cell P
  have ha := active_numbers hcut hactive (reach_shrink hroot hreach)
  obtain ⟨G,hG,cert,_⟩ := active_packing row col ha hr hc
  refine ⟨G,hG,cert,?_⟩
  intro j g M'
  have hnew : ReachSize M0 (d+1) M' := .child hreach (group_wire_shrink G.cell cert j g)
  exact ⟨hnew,child_old_degree G.cell j g row col _ hr hc,
    fun v => (child_packet_degree G j g v).trans ha.packetPorts,
    fun h => active_numbers hcut h (reach_shrink hroot hnew)⟩

#print axioms active_step
#check @RootSeparation.Preprocessing.active_step
#check @RootSeparation.Preprocessing.hermite_mass


theorem one_positive_clique :
    let E' := Entry.survivingEdges (cliques 1) (fun v => decide (v.2 = 0))
    E'.card = 3 ∧ triple E' = 0 ∧ builtM E' = 20 := by
  intro E'
  rw [builtM_eq]
  decide

#print axioms one_positive_clique


theorem entry_dispatch_exact (E : Finset (V × V)) (simple : Entry.Simple E)
    (reg : ∀ v, degree E v = 3) (σ : V → Bool) :
    dispatch (simpleNormalize (PinnedCNF.formula E σ)) =
      if n (V := V) = 0 then .free else if n (V := V) < 20 then .enumerate else .sparse := by
  classical
  rw [simpleNormalize_pinned E simple σ]
  by_cases hl : n (V := V) < 20
  · have hf : (PinnedCNF.formula E σ).filter (fun c => !decide (Tautological c)) =
      PinnedCNF.formula E σ :=
      List.filter_eq_self.mpr fun c hc => by simp [(no_trivial_clause E σ c hc).2]
    have he : [] ∉ PinnedCNF.formula E σ := fun h => (no_trivial_clause E σ [] h).1 rfl
    have hm := formula_length E σ
    have hC := (dimensions E reg).1
    by_cases hN : n (V := V) = 0
    · have hz : (PinnedCNF.formula E σ).length = 0 := by omega
      have hf0 : PinnedCNF.formula E σ = [] := List.length_eq_zero_iff.mp hz
      simp [dispatch,hf0,hN]
    · have hne : PinnedCNF.formula E σ ≠ [] := by
        intro h
        rw [h,List.length_nil] at hm
        unfold m at hm
        omega
      simp [dispatch,hf,he,hne,hN,hl]
  · have hn : 20 ≤ n (V := V) := by omega
    simp [dispatch_pinned E reg σ hn,hl,show n (V := V) ≠ 0 by omega]

theorem sparse_root_degrees (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (checks : ActiveNumbers (size E) 0 (rootM E)) :
    (∀ v, fiberCount (row E reg) v ≤ degreeEnvelope (size E)) ∧
    (∀ v, fiberCount (column E) v ≤ degreeEnvelope (size E)) :=
  ⟨fun v => (row_degree E reg v).trans checks.degreeCover,
    fun v => by rw [col_degree]; exact (by decide : 2 ≤ 3).trans checks.degreeCover⟩

#print axioms entry_dispatch_exact
#print axioms sparse_root_degrees
#check @RootSeparation.Preprocessing.entry_dispatch_exact

end RootSeparation.Preprocessing

