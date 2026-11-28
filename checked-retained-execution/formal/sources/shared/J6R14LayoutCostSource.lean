import J6R14LayoutCostDriver
import J6R14LayoutCostRound
import J6R12CollisionPacking

/-! Same selected labels, same physical ordered fibres: connect the
paid grouping to the R12 output edge tape, without assuming a
canonical inverse to an arbitrary label code. -/

namespace J6R14LayoutCost
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionBits J6R12CollisionEdges
open J6R12CollisionMenu J6R12CollisionSource J6R12CollisionGreedyStep J6R12CollisionPacking
open J6R11Collision J6R11CollisionReindex J6R10Repack P11FullPacking

variable {E R C A : Type*} [Fintype E] [Fintype A]

def codePair (F : Format E R C A) (x : A×A) : CellWord :=
  (F.label x.1,F.label x.2)

theorem codePair_inj (F : Format E R C A) : Function.Injective (codePair F) := by
  have hF : Function.Injective F.label := by
    intro x y h
    apply F.aInj
    have he := congrArg bitsValue h
    change bitsValue (encodeBits F.b (F.aCode x)) = bitsValue (encodeBits F.b (F.aCode y)) at he
    simpa only [encodeBits_exact _ _ (F.aFit _)] using he
  intro x y h
  exact Prod.ext (hF (congrArg Prod.fst h)) (hF (congrArg Prod.snd h))

theorem codePair_mem (F : Format E R C A) (x : A×A) : codePair F x∈allPairs F.b := by
  apply (allPairs_mem _ _).mpr
  exact ⟨encodeBits_length _ _,encodeBits_length _ _⟩

theorem codePair_cover (F : Format E R C A) (hsize : Fintype.card A=2^F.b)
    (k : CellWord) (hk : k∈allPairs F.b) : ∃ x : A×A,codePair F x=k := by
  obtain ⟨u,us,hm,_,_,_⟩ := full_alphabet F hsize
  have he : (u::us).map F.label=binaryMenu F.b := hm.symm.trans (menuMachine_exact _).1
  obtain ⟨hL,hR⟩ := (pairsSpec_mem _ _ _).mp hk
  rw [← he] at hL hR
  obtain ⟨x,_,hx⟩ := List.mem_map.mp hL
  obtain ⟨y,_,hy⟩ := List.mem_map.mp hR
  exact ⟨(x,y),Prod.ext hx hy⟩

def graphWord (F : Format E R C A) (z : R⊕C→A) (e : E) : EdgeTape :=
  packEdge F.kR F.kC F.b F.rCode F.cCode F.aCode F.row F.col (fun i=>some (z i)) e

def sourceCell (F : Format E R C A) (z : R⊕C→A) (e : E) : A×A :=
  (z (.inl (F.row e)),z (.inr (F.col e)))

theorem graphWord_cell (F : Format E R C A) (z : R⊕C→A) (e : E) :
    rawCell (graphWord F z e)=some (codePair F (sourceCell F z e)) := rfl

theorem graphWord_widths (F : Format E R C A) (z : R⊕C→A) :
    ∀ e∈F.graph (fun i=>some (z i)),labelWidths F.b e := by
  intro t ht
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp ht
  constructor
  · intro u hu
    change some (encodeBits F.b (F.aCode (z (.inl (F.row e)))))=some u at hu
    rw [← Option.some.inj hu,encodeBits_length]
  · intro v hv
    change some (encodeBits F.b (F.aCode (z (.inr (F.col e)))))=some v at hv
    rw [← Option.some.inj hv,encodeBits_length]

theorem sourceBucket_length (F : Format E R C A) (z : R⊕C→A) (q : ℕ) (x : A×A) :
    (bucket Tagged.edge (codePair F x) (tagSpec q 0 (F.graph (fun i=>some (z i))))).length
      =Nat.card (Fiber (sourceCell F z) x) := by
  rw [← List.length_map (f := Tagged.edge),bucket_tags]
  change (bucket id (codePair F x) (F.edges.map (graphWord F z))).length=_
  have hf : bucket id (codePair F x) (F.edges.map (graphWord F z))=
      (F.edges.filter (fun e => decide (sourceCell F z e=x))).map (graphWord F z) := by
    generalize F.edges=es
    induction es with
    | nil => rfl
    | cons e es ih =>
      have H : (rawCell (graphWord F z e)=some (codePair F x)) ↔ sourceCell F z e=x := by
        rw [graphWord_cell,Option.some.injEq,(codePair_inj F).eq_iff]
      by_cases h : sourceCell F z e=x
      · simp [bucket,h,H.mpr h] at ih ⊢
        exact ih
      · have hh := H.not.mpr h
        simp [bucket,h,hh] at ih ⊢
        exact ih
  rw [hf,List.length_map]
  let l := F.edges.filter (fun e => decide (sourceCell F z e=x))
  have hn : l.Nodup := F.edgesNodup.filter _
  have hset : l.toFinset=fibre (sourceCell F z) x := by
    ext e
    simp [l,fibre,F.edgesAll e]
  change l.length=_
  rw [← List.toFinset_card_of_nodup hn,hset,card_filter_fibre]

theorem peakSource_exact (F : Format E R C A) (hsize : Fintype.card A=2^F.b)
    (z : R⊕C→A) (q : ℕ) :
    peak Tagged.edge (tagSpec q 0 (F.graph (fun i=>some (z i)))) (allPairs F.b)=
      maxFiber (sourceCell F z) := by
  apply le_antisymm
  · apply peak_le
    intro k hk
    obtain ⟨x,rfl⟩ := codePair_cover F hsize k hk
    rw [sourceBucket_length]
    exact fiber_le_max _ _
  · unfold maxFiber
    apply Finset.sup_le
    intro x _
    rw [← sourceBucket_length F z q x]
    exact bucket_le_peak _ _ _ _ (codePair_mem F x)

omit [Fintype E] in
theorem maxFiber_transport {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X≃Y) (f : E→X) : maxFiber (fun u => e (f u))=maxFiber f := by
  have h (x : X) : Nat.card (Fiber (fun u=>e (f u)) (e x))=Nat.card (Fiber f x) :=
    Nat.card_congr {
      toFun := fun u => ⟨u.val,e.injective u.property⟩
      invFun := fun u => ⟨u.val,congrArg e u.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  apply le_antisymm
  · apply Finset.sup_le
    intro y _
    obtain ⟨x,rfl⟩ := e.surjective y
    rw [h]
    exact fiber_le_max _ _
  · apply Finset.sup_le
    intro x _
    rw [← h]
    exact fiber_le_max _ _

#print axioms codePair_inj
#print axioms sourceBucket_length
#print axioms peakSource_exact
#print axioms maxFiber_transport
end J6R14LayoutCost

