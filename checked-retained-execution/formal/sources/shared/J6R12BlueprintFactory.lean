import J6R12BlueprintSite
import J6R12BlueprintPacket
import J6R10ReachableDependent
import J6R10IntegralFinite

/-! Literal dependent slots and the actual compiled packet factory.
The data of a generated child are computed here from its native address;
they are not an equality supplied for each child. The fallback on a raw
call that fails the source guard has no claimed source interpretation. -/
namespace J6R12Blueprint
open scoped Classical Polynomial
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R11Blueprint
  J6R10Reachable J6R10Repack J6R11Repack

variable {f : ℤ[X]} {ell : ℕ}
variable (S : Params (f:=f) (ell:=ell)) (Δ : ℕ) (sel : Selector S Δ)

noncomputable def modeAt (c : Call (H (f:=f) (ell:=ell))) (t : Center S c) : Type :=
  if d : Ready S Δ c then SiteMode sel d t else PEmpty

theorem modeAt_eq {c : Call (H (f:=f) (ell:=ell))} (d : Ready S Δ c) (t : Center S c) :
    modeAt S Δ sel c t = SiteMode sel d t := by
  simp [modeAt,d]

noncomputable def weightAt (c : Call (H (f:=f) (ell:=ell))) (t : Center S c)
    (m : modeAt S Δ sel c t) : ℕ :=
  if d : Ready S Δ c then siteWeight sel d t ((Equiv.cast (modeAt_eq S Δ sel d t)) m) else 1

theorem weightAt_pos (c : Call (H (f:=f) (ell:=ell))) (t : Center S c)
    (m : modeAt S Δ sel c t) : 0 < weightAt S Δ sel c t m := by
  unfold weightAt
  split
  · exact siteWeight_pos sel _ _ _
  · decide

theorem weightAt_mode {c : Call (H (f:=f) (ell:=ell))} (d : Ready S Δ c) (t : Center S c)
    (m : SiteMode sel d t) :
    weightAt S Δ sel c t ((Equiv.cast (modeAt_eq S Δ sel d t)).symm m) =
      siteWeight sel d t m := by
  simp only [weightAt,dif_pos d,Equiv.apply_symm_apply]

noncomputable def shape : NativeShape (H (f:=f) (ell:=ell)) where
  params := S
  Mode := modeAt S Δ sel
  finiteMode := fun c t => by
    unfold modeAt
    split <;> infer_instance
  decideMode := fun _ _ => Classical.decEq _
  weight := weightAt S Δ sel

variable {S Δ}
variable {c : Call (H (f:=f) (ell:=ell))}

noncomputable def packetOfSite (d : Ready S Δ c) (t : Center S c) (z : Probe S c)
    (β : SiteMode sel d t →₀ ℕ) (g : Fin 64) : H (f:=f) (ell:=ell) := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  let p := registerPrecision S c t
  exact actualPacketHost (packing sel d) (centerIndex d t) (centerNonzero t) rfl
    p (J6R10Integral.box_two_nil p f ell) (sampleNode S f ell c d.fit t z)
    c.host.file β g

theorem packetOfSite_shrinks (d : Ready S Δ c) (t : Center S c) (z : Probe S c)
    (β : SiteMode sel d t →₀ ℕ) (g : Fin 64) :
    32*(packetOfSite sel d t z β g).edgeCount ≤ 3*c.edges := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  rw [← d.edgeCount]
  apply actualPacketHost_shrinks _ _ _ _ _ _ _ _ _ _ (Fintype.card_fin 64)
  change 0 < c.host.edgeCount
  rw [d.edgeCount]
  exact Nat.zero_lt_of_lt d.active

noncomputable def siteTuple (d : Ready S Δ c) (w : NativeAddress (shape S Δ sel) c) :
    SiteMode sel d w.1 →₀ ℕ :=
  Finsupp.embDomain (Equiv.cast (modeAt_eq S Δ sel d w.1)).toEmbedding w.2.2.1.val

noncomputable def payload (S : Params (f:=f) (ell:=ell)) (Δ : ℕ) (sel : Selector S Δ)
    (c : Call (H (f:=f) (ell:=ell))) (w : NativeAddress (shape S Δ sel) c) :
    H (f:=f) (ell:=ell) × ℕ :=
  if d : Ready S Δ c then
    let host := packetOfSite sel d w.1 w.2.1 (siteTuple sel d w) w.2.2.2
    (host,host.edgeCount)
  else (c.host,0)

theorem payload_exact (d : Ready S Δ c) (w : NativeAddress (shape S Δ sel) c) :
    payload S Δ sel c w =
      let host := packetOfSite sel d w.1 w.2.1 (siteTuple sel d w) w.2.2.2
      (host,host.edgeCount) := by
  simp only [payload,dif_pos d]

noncomputable def children (S : Params (f:=f) (ell:=ell)) (Δ : ℕ) (sel : Selector S Δ) :
    NativeChildren (shape S Δ sel) where
  host c w := (payload S Δ sel c w).1
  edges c w := (payload S Δ sel c w).2
  bound := by
    intro c _ w
    by_cases d : Ready S Δ c
    · rw [payload_exact sel d]
      exact packetOfSite_shrinks sel d w.1 w.2.1 (siteTuple sel d w) w.2.2.2
    · simp [payload,d]

theorem child_exact (d : Ready S Δ c) (w : NativeAddress (shape S Δ sel) c) :
    (nativePlan (shape S Δ sel) (children S Δ sel)).child c ⟨w,d.active⟩ =
      let host := packetOfSite sel d w.1 w.2.1 (siteTuple sel d w) w.2.2.2
      ⟨host,c.depth+1,host.edgeCount,registerPrecision S c w.1⟩ := by
  unfold nativePlan children
  simp only [payload_exact sel d]
  rfl

#print axioms modeAt_eq
#print axioms weightAt_pos
#print axioms weightAt_mode
#print axioms packetOfSite_shrinks
#print axioms payload_exact
#print axioms child_exact
end J6R12Blueprint