import J6R14LayoutCostMenu

/-! The priced ordered-cell grouping driver. Starting from a labeled
edge tape, it writes occurrence IDs, generates every legal key from
scratch, and scans and writes every bucket and its maximum load. -/

namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionEdges J6R12CollisionMenu

def allPairs (b : ℕ) : List CellWord := pairsSpec (binaryMenu b) (binaryMenu b)

def allPairsCap (b : ℕ) : ℕ :=
  16*(b+1)*2^b + 2^b*((8*b+22)*2^b+4)+4

def allPairsMachine (b : ℕ) : Meter (List CellWord) :=
  let m := menuMachine b
  let q := pairMenu b m.result m.result
  ⟨q.result,m.steps+q.steps+4⟩

theorem allPairsMachine_exact (b : ℕ) :
    (allPairsMachine b).result=allPairs b ∧ (allPairsMachine b).steps≤allPairsCap b := by
  obtain ⟨he,hc⟩ := menuMachine_exact b
  obtain ⟨hp,hpc⟩ := pairMenu_exact b (menuMachine b).result (menuMachine b).result
  unfold allPairsMachine
  dsimp only
  rw [he,binary_length] at hpc
  refine ⟨by rw [hp,he,allPairs],?_⟩
  rw [he]
  exact Nat.add_le_add_right (Nat.add_le_add hc hpc) _

theorem allPairs_len (b : ℕ) : (allPairs b).length=2^b*2^b := by
  simp only [allPairs,pairsSpec_length,binary_length]

theorem allPairs_mem (b : ℕ) (k : CellWord) :
    k∈allPairs b ↔ k.1.length=b ∧ k.2.length=b := by
  rw [allPairs,pairsSpec_mem,binary_mem,binary_mem]

theorem allPairs_nodup (b : ℕ) : (allPairs b).Nodup :=
  pairsSpec_nodup _ _ (binary_nodup _) (binary_nodup _)

def orderedTapeCap (kR kC b q M : ℕ) : ℕ :=
  M*tagStepCap kR kC b q+q+2+allPairsCap b+
    (q+2+2^b*2^b*boxStepCap kR kC b q M)+6

def orderedTape (kR kC b q : ℕ) (es : List EdgeTape) : Meter (List (Box Tagged) × List Bool) :=
  let u := tagAll kR kC b q es
  let v := allPairsMachine b
  let t := groupAll Tagged.edge kR kC b q u.result v.result
  ⟨t.result,u.steps+v.steps+t.steps+6⟩

theorem orderedTape_exact (kR kC b q : ℕ) (hq : 0<q) (es : List EdgeTape)
    (hf : es.length<2^q) (H : ∀ e∈es,labelWidths b e) :
    let u := orderedTape kR kC b q es
    u.result.1=(allPairs b).map (boxSpec Tagged.edge q (tagSpec q 0 es)) ∧
    u.result.2.length=q ∧ bitsValue u.result.2=peak Tagged.edge (tagSpec q 0 es) (allPairs b) ∧
      u.steps≤orderedTapeCap kR kC b q es.length := by
  obtain ⟨hr,hc⟩ := tagAll_exact kR kC b q hq es hf
  obtain ⟨he,hs⟩ := allPairsMachine_exact b
  have hf' : (tagSpec q 0 es).length<2^q := by rwa [tagSpec_length]
  have ht : ∀ r∈tagSpec q 0 es,labelWidths b r.edge := by
    intro r hm
    apply H
    rw [← tagSpec_edge q 0 es]
    exact List.mem_map.mpr ⟨r,hm,rfl⟩
  obtain ⟨h₁,h₂,h₃,h₄⟩ := groupAll_exact Tagged.edge kR kC b q hq (tagSpec q 0 es) hf' ht
    (allPairs b) (fun k hk => (allPairs_mem b k).mp hk)
  unfold orderedTape
  dsimp only
  rw [hr,he]
  rw [tagSpec_length,allPairs_len] at h₄
  exact ⟨h₁,h₂,h₃,Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc hs) h₄) _⟩

theorem bucket_tags (q j : ℕ) (k : CellWord) (es : List EdgeTape) :
    (bucket Tagged.edge k (tagSpec q j es)).map Tagged.edge=bucket id k es := by
  induction es generalizing j with
  | nil => rfl
  | cons x xs ih =>
    have I := ih (j+1)
    unfold bucket at I
    cases h : decide (rawCell x=some k) <;> simp [bucket,tagSpec,h,I]

#print axioms allPairsMachine_exact
#print axioms allPairs_nodup
#print axioms orderedTape_exact
#print axioms bucket_tags
end J6R14LayoutCost

