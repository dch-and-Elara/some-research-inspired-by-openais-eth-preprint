import J6R15PlantedIdentityMesh
import J6R15PlantedIdentityTables
import J6R15PlantedIdentityRational
import J6R12RepackRootReady

/-! The actual root's native polynomial at the odd mesh centre and the
omitted zero probe is the finite image of the repaired J2 scalar. -/
namespace J6R15PlantedIdentity
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6Mesh J6OrientedHost J6OrientedHostEval J6RepairedCentered
open J6R10Repack J6R10Integral J6R11Integral J6R11Repack J6R12Repack J6R9Recursive
open J6R11Blueprint J6R12Blueprint J6ActiveRun J1PPrinted
noncomputable section

variable {S V : Type} [LinearOrder S] [Fintype S] [Fintype V]

set_option maxHeartbeats 3800000 in
theorem root_parent_at_zero
    (f : ℤ[X]) (ell base p m l q : ℕ) (T : Plant V m q)
    (w : Fin (a m) → S) (mask : MaskFamily (a m) (K m) S)
    (hm : m≤K m) (hL : 2*l=L m) (hS : Fintype.card S=64)
    (i : Fin (m+1)) (hf : f.Monic) (hbase : 0<base) (hF : 0<f.natDegree) (hℓ : 0<ell) :
    ((parentJet (rootPacking m l q T w mask hm hL hS) (rootEntryFile f ell base T w) hf
      (index m i : ℤ)).map (reduce p f ell)).eval 0 =
      J6ZeroTransport.reduceAt p (box_two_nil p f ell) (plantedScalar m l q T w mask hm hL i) := by
  rw [parentJet,network_finite]
  let E := Ports m l w
  let N := rootNetwork (b:=K m) (l:=l) T w
  let file := rootEntryFile (b:=K m) (l:=l) f ell base T w
  have hleft : (reduce p f ell) ∘ rowProduct N file hf = fun y : E→Bool =>
      if oldOK T w y then 1 else 0 :=
    funext (old_table_receives f ell base p T w hf hbase hF hℓ)
  have hright : (reduce p f ell) ∘ colProduct N file hf = fun x : E→Bool =>
      if newOK T w x then 1 else 0 :=
    funext (new_table_receives f ell base p T w hf hbase hF hℓ)
  change J6R10Integral.contract _ ((reduce p f ell) ∘ rowProduct N file hf)
    ((reduce p f ell) ∘ colProduct N file hf) = _
  rw [hleft,hright,contract_flags,plantedScalar_receives]
  have hw := funext (fun r => funext (mesh_kernel_at_zero f ell p m l q T w mask hm hL hS i r))
  rw [hw,J6ZeroTransport.contraction_of_partial]

theorem root_parent_at_zero_cast
    (f : ℤ[X]) (ell base p m l q : ℕ) (T : Plant V m q)
    (w : Fin (a m) → S) (mask : MaskFamily (a m) (K m) S)
    (hm : m≤K m) (hL : 2*l=L m) (hS : Fintype.card S=64)
    (i : Fin (m+1)) (hf : f.Monic) (hbase : 0<base) (hF : 0<f.natDegree) (hℓ : 0<ell)
    (n : ℕ) (hn : a m=n) :
    ((parentJet (show PhysicalPacking (rootNetwork (b:=K m) (l:=l) T w) n S from
      hn ▸ rootPacking m l q T w mask hm hL hS)
      (rootEntryFile f ell base T w) hf (index m i : ℤ)).map (reduce p f ell)).eval 0 =
      J6ZeroTransport.reduceAt p (box_two_nil p f ell) (plantedScalar m l q T w mask hm hL i) := by
  subst n
  exact root_parent_at_zero f ell base p m l q T w mask hm hL hS i hf hbase hF hℓ

private theorem selected_cast {f : ℤ[X]} {ell : ℕ} {H : PhysicalHost f ell} {G : Type} [LinearOrder G] [Fintype G]
    {a b : ℕ} (h : a=b) (P : Selected H a G) :
    (show Selected H b G from h ▸ P).packing =
      (show PhysicalPacking H.network b G from h ▸ P.packing) := by
  subst b
  rfl

section ExactSource
variable {f : ℤ[X]} {ell : ℕ}
variable (base m l q native : ℕ) (T : Plant V m q)
variable (w : Fin (a m) → Fin 64) (mask : MaskFamily (a m) (K m) (Fin 64))
variable (hm : m≤K m) (hL : 2*l=L m) (hn : native≤m)
variable (d : Ready (rootParams f ell m native) (sourceDelta (physicalSize m native))
  (physicalRootCall f ell base m l q T w))

set_option maxHeartbeats 5500000 in
theorem selected_parent_at_odd
    (i : Fin (m+1)) (hf : f.Monic) (hbase : 0<base) (hF : 0<f.natDegree) (hℓ : 0<ell) :
    let c := physicalRootCall f ell base m l q T w
    let sel := exactJ6Selector (f:=f) (ell:=ell) base m l q native T w mask hm hL hn
    let t := oddRootCenter f ell base m l q native T w hn i
    let p := registerPrecision (rootParams f ell m native) c t
    letI := c.host.finiteEdge
    letI := c.host.finiteRow
    letI := c.host.finiteCol
    ((parentJet (packing sel d) c.host.file hf t.val).map (reduce p f ell)).eval 0 =
      J6ZeroTransport.reduceAt p (box_two_nil p f ell) (plantedScalar m l q T w mask hm hL i) := by
  let c := physicalRootCall f ell base m l q T w
  let Sₚ := rootParams f ell m native
  let t := oddRootCenter f ell base m l q native T w hn i
  let p := registerPrecision Sₚ c t
  let sel := exactJ6Selector (f:=f) (ell:=ell) base m l q native T w mask hm hL hn
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  change ((parentJet (packing sel d) c.host.file hf (index m i : ℤ)).map (reduce p f ell)).eval 0 = _
  have hbits : Sₚ.levelBits 0 = a m := mesh_root_bits m native hn
  have hP :
      packing sel d =
        (actualSelectedAtSchedule f ell base m l q T w mask hm hL (Fintype.card_fin 64)
          Sₚ.levelBits hbits).packing :=
    actual_j6_root_pinned Sₚ (sourceDelta (physicalSize m native)) base m l q T w
      mask hm hL hbits d
  rw [hP]
  have hseat :
      (actualSelectedAtSchedule f ell base m l q T w mask hm hL (Fintype.card_fin 64)
        Sₚ.levelBits hbits).packing =
        (show PhysicalPacking c.host.network (Sₚ.levelBits 0) (Fin 64) from
          hbits.symm ▸ rootPacking m l q T w mask hm hL (Fintype.card_fin 64)) :=
    selected_cast hbits.symm (actualSelectedRoot f ell base m l q T w mask hm hL (Fintype.card_fin 64))
  rw [hseat]
  exact root_parent_at_zero_cast f ell base p m l q T w mask hm hL (Fintype.card_fin 64)
    i hf hbase hF hℓ (Sₚ.levelBits 0) hbits.symm

end ExactSource

#print axioms root_parent_at_zero
#print axioms root_parent_at_zero_cast
#print axioms selected_parent_at_odd
end
end J6R15PlantedIdentity
