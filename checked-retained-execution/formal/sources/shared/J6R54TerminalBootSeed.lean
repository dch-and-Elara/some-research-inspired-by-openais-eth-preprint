import J6R41StructuredAllPathsRoot
import J6R53TerminalGateGeometry
import J6R49LeafOriginal
import J6R27OriginalGateRun

/-! At the actual printed exterior there are exactly the original
old vertices and the originally emitted Pages. R41 has already
proved the exact port bodies and tags on the paid root publication.
Here the stored original Gate syntax is put beside the same typed
origin, including a degree-zero owner. -/
namespace J6R54TerminalBoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R36ChildFramedRoute J6R41StructuredAllPaths J6R53TerminalGate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 38000000
set_option maxRecDepth 5300
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}

def printedGateCode (P : Plant V m n) (x : SourceVertex P) : CodeGate (Word (pageKeyWidth m+a m)) :=
  let D := originalPortGate P (J6R28GeneratedRootFrame.constantRootWord m) x
  encodeGate (rootSuffixAt (f:=f) (ell:=ell) (base:=base) P x∘D.port) D.gate

variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)

def bootGates (u : (ext).host.Row⊕(ext).host.Col) : Option (CodeGate (Word (pageKeyWidth m+a m))) :=
  match u with
  | .inl old=>some (printedGateCode (f:=f) (ell:=ell) (base:=base) P old.val)
  | .inr _=>none

variable (gate : Stamp key prec) (pad : ℕ)

def InitialGateSource (u : (ext).host.Row⊕(ext).host.Col) : Prop :=
  ∃ x : SourceVertex P,
    ∃ tr : Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) x) (J6R34ChildPath.point (ext).host u),
    bootGates X u=some (printedGateCode (f:=f) (ell:=ell) (base:=base) P x) ∧
    ∀ h : PortAt (J6R34ChildPath.point (ext).host u),
      initialPayload X gate pad h.val=
        (initialOrigin X gate pad u,tr.literal (rootGateBody x) h)

def InitialPageSource (u : (ext).host.Row⊕(ext).host.Col) : Prop :=
  ∃ k : CanonicalPage m,
    ∃ tr : Trace (stableBorn X k) (J6R34ChildPath.point (ext).host u),
    bootGates X u=none ∧ initialOrigin X gate pad u=exteriorPageOrigin X pad k ∧
    ∀ h : PortAt (J6R34ChildPath.point (ext).host u),
      initialPayload X gate pad h.val=
        (initialOrigin X gate pad u,tr.literal (originSeed (rootChart P) (oddAxis m) X.group k) h)

theorem exact_initial_payload_gate_or_page (gateWidth : gate.created.val=base)
    (u : (ext).host.Row⊕(ext).host.Col) :
    InitialGateSource X gate pad u ∨ InitialPageSource X gate pad u := by
  cases u with
  | inl old =>
    obtain ⟨tr,h⟩ := initial_gate_is_written X gate pad gateWidth old
    exact Or.inl ⟨old.val,tr,rfl,h⟩
  | inr page =>
    let E := canonicalPageEquiv G ell X.centre
    obtain ⟨k,rfl⟩ := E.surjective page
    obtain ⟨tr,_,h⟩ := initial_packet_is_written X gate pad k
    have tag : initialOrigin X gate pad (.inr (E k))=exteriorPageOrigin X pad k := by
      change exteriorPageOrigin X pad (E.symm (E k))=_
      rw [Equiv.symm_apply_apply]
    exact Or.inr ⟨k,tr,rfl,tag,h⟩

theorem exact_boot_port_uses_the_same_owner_tag (gateWidth : gate.created.val=base)
    (u : (ext).host.Row⊕(ext).host.Col) (h : PortAt (J6R34ChildPath.point (ext).host u)) :
    (initialPayload X gate pad h.val).1=initialOrigin X gate pad u := by
  rcases exact_initial_payload_gate_or_page X gate pad gateWidth u with old|new
  · obtain ⟨x,tr,code,body⟩ := old
    exact congrArg Prod.fst (body h)
  · obtain ⟨k,tr,code,stamp,body⟩ := new
    exact congrArg Prod.fst (body h)

end
#print axioms exact_initial_payload_gate_or_page
#print axioms exact_boot_port_uses_the_same_owner_tag
end J6R54TerminalBoot
