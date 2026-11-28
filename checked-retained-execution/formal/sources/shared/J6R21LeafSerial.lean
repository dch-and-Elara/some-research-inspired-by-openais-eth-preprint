
import J6R21LeafPlant
import J6R21LeafPrintedStop

/-! Fully concrete original-source leaf on its sequential descriptor
file. No array lookup or counted #SAT subroutine remains at the leaf.
Layout construction and writing the static descriptor/address file
are a preceding operation, not quietly included in these read costs. -/
namespace J6R21Leaf
open scoped BigOperators Polynomial Classical
open Polynomial AOracleMachineTime AOracleCoordinates A1R10 A1R11 A1R12
open J6ActiveRun J6R9Recursive J6R10Repack J6R11Blueprint J6R11Repack J6OrientedHost
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9000000

theorem plant_degree_bound {S V : Type} [LinearOrder S] {a b m q l n D : ℕ}
    (T : Plant V m q) (w : Fin a→S) (slot : Wire w m b l→Fin n)
    (dOld : ∀ v,T.degree v≤D) (hd : 2≤D)
    (v : Left V w m b l⊕Right w m b l q) :
    (plantIndexedGate T w slot v).degree≤D := by
  rcases v with ((⟨s,j⟩|⟨pad,tag⟩)|v)
  · exact dOld s
  · exact (by decide : (1:ℕ)≤2).trans hd
  · exact hd

theorem original_fee_mono (m k : ℕ) {d D : ℕ} (h : d≤D) :
    originalGateFee m k d≤originalGateFee m k D := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _

noncomputable def vertexList {f : ℤ[X]} {ell : ℕ} (H : PhysicalHost f ell) :
    List (H.Row⊕H.Col) := by
  letI := H.finiteRow
  letI := H.finiteCol
  exact (Finset.univ : Finset (H.Row⊕H.Col)).toList

theorem vertexList_nodup {f : ℤ[X]} {ell : ℕ} (H : PhysicalHost f ell) :
    (vertexList H).Nodup := by
  classical
  unfold vertexList
  exact Finset.nodup_toList _

theorem vertexList_complete {f : ℤ[X]} {ell : ℕ} (H : PhysicalHost f ell) (v : H.Row⊕H.Col) :
    v∈vertexList H := by
  classical
  simp [vertexList]

theorem physical_plant_leaf_from_serial_file {S V : Type} [LinearOrder S] [Fintype S] [Fintype V]
    {f : ℤ[X]} (ell p m l q : ℕ) (T : Plant V m q) (w : Fin (J6Mesh.a m)→S)
    (hp : 0<p) {fw : List (A1R10.Word p)} (he : 0<fw.length) (hℓ : 0<ell)
    (hPoly : Modulus p hp fw=NativeProbeRing.liftPoly p f) (hf : f.Monic)
    (count : (physicalRootCall f ell p m l q T w).host.edgeCount=
      (physicalRootCall f ell p m l q T w).edges)
    (k : ℕ) (fit : (physicalRootCall f ell p m l q T w).edges≤2^k)
    (D : ℕ) (dOld : ∀ v,T.degree v≤D) (hd : 2≤D) :
    let c := physicalRootCall f ell p m l q T w
    let vertices := vertexList c.host
    let slot := c.host.edgeOrder c.edges count
    ∀ descriptorFile : List (OriginalGateTape c.edges k),
      descriptorFile=vertices.map (fun v=>(plantIndexedGate T w slot v).tape fit) →
      let out := leafCompute hp he hℓ c.edges descriptorFile (uvGate hp he hℓ)
      J6R18ChildWrite.castBox hPoly (uvRead hp fw ell out.result)=reduce p f ell (c.host.contract hf) ∧
      out.steps≤callLeafFee fw.length ell p c.edges vertices.length
        (originalGateFee c.edges k D+uvWidth fw.length ell p+4) hp := by
  dsimp only
  intro descriptorFile ordered
  rw [ordered,leafCompute_mapped]
  let c := physicalRootCall f ell p m l q T w
  let xs := vertexList c.host
  let slot := c.host.edgeOrder c.edges count
  let Q := plantReader T w hp he hℓ slot fit
  change J6R18ChildWrite.castBox hPoly (uvRead hp fw ell
    (leafCompute hp he hℓ c.edges xs Q).result)=reduce p f ell (c.host.contract hf) ∧
      (leafCompute hp he hℓ c.edges xs Q).steps≤_
  constructor
  · exact actual_leaf_exact c hp he hℓ hPoly hf count xs (vertexList_nodup _) (vertexList_complete _) Q
      (plant_query_at_physical_root ell p m l q T w hp he hℓ hPoly hf count k fit)
  · refine leaf_compute_uniform_fee hp he hℓ c.edges xs Q _ ?_
    intro x v _
    have h := (plant_reader_exact T w hp he hℓ slot fit x v).2
    have dm := original_fee_mono c.edges k (plant_degree_bound T w slot dOld hd v)
    exact h.trans (Nat.add_le_add_right (Nat.add_le_add_right dm _) _)

#print axioms plant_degree_bound
#print axioms original_fee_mono
#print axioms vertexList_nodup
#print axioms vertexList_complete
#print axioms physical_plant_leaf_from_serial_file
end J6R21Leaf
