import J6R19RetainedPromote

/-! Actual retained branch of the physical child. The hypothesis is the
old evaluator's already-supplied creation-time frame at REINDEXED
ports; no implementation-cost claim is made for obtaining that frame. -/
namespace J6R19Retained
open scoped Polynomial
open A1R10 AOracleMachineTime J6R18ChildWrite
open J6R10Repack J6R11Blueprint P11FullPacking J6R9PacketScopes J6R9PacketChild

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}

set_option maxHeartbeats 1000000 in
theorem paid_retained_host_read {q ell oldWidth newWidth : ℕ} {f : ℤ[X]}
    (hf : f.Monic) (he : 0<f.natDegree) (hq : 0<q)
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (hnil : (2:Residue f ell q)^q=0) (z : Residue f ell q)
    (oldFile : EntryFile f ell N) (β : Mode i q P.mask→₀ℕ) (g : G) (v : Old (atGroup P i) g)
    (hp : 0<(oldFile v.val).created)
    {old : List (Word (oldFile v.val).created)} {new : List (Word q)}
    (hO : Modulus (oldFile v.val).created hp old=NativeProbeRing.liftPoly (oldFile v.val).created f)
    (hN : Modulus q hq new=NativeProbeRing.liftPoly q f)
    (fromTag : J6R15ModeCost.Word oldWidth) (htO : fromTag.val=(oldFile v.val).created)
    (toTag : J6R15ModeCost.Word newWidth) (htN : toTag.val=q) :
    let host := actualPacketHost P i ht hv q hnil z oldFile β g
    ∀ bits : ParentPorts host.network (.inl v)→Bool, ∀ input : UVBlock old ell,
    castBox hO (uvRead hp old ell input)=
      (oldFile v.val).table (bits ∘ (oldReindex N (atGroup P i) (atPacket P) g v).symm) →
    ∀ suffix : List Bool,
    let hE := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
    let out := promoteFrame (ell:=ell) (oldWidth:=oldWidth) hE toTag ((writeEntry fromTag input).result++suffix)
    ∃ u : UVBlock new ell,
      out.result=((writeEntry toTag u).result,suffix) ∧
      fromTag.val=(host.file (.inl v)).created ∧ toTag.val=q ∧
      frameRead newWidth q new.length ell out.result.1=(toTag.bits,u.val.map (fun row=>row.val.map Subtype.val)) ∧
      castBox hN (uvRead hq new ell u)=(host.file (.inl v)).read hf q bits ∧
      out.steps≤promoteFee f.natDegree ell (oldFile v.val).created q oldWidth newWidth := by
  intro host bits input hEntry suffix
  let oldBits := bits ∘ (oldReindex N (atGroup P i) (atPacket P) g v).symm
  exact promote_frame_native hf he hq (oldFile v.val) hp hO hN fromTag htO toTag htN
    oldBits input hEntry suffix

#print axioms paid_retained_host_read
end J6R19Retained


