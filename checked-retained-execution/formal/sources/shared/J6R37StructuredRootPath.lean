import J6R37StructuredRootChain
import J6R35RootOriginsFrontier

/-! Apply the real occurrence-Path induction to the physically emitted
initial records. For a native origin this theorem preserves the same
occurrence witness; R36 supplies its one-step writer once the actual
layout/addon inputs are available. It does not assert those inputs are
automatically materialized throughout the recursion. -/
namespace J6R37StructuredRoot
open scoped Polynomial Classical
open Polynomial J6R21Ancestor J6R34ChildPath J6R35RootOrigins
open J6R36ChildFramedRoute J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R31RootResidentTables J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack
open J6R27PrescribedProbe J6R26StablePreparedRoot J6R11Repack J6R25PreparedSupply J6R26DescriptorTree
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6ActiveRun J6R12Blueprint J6R11Blueprint J1PPrinted J6R16ModeCost
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 21000000
set_option maxRecDepth 3000

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw C s : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)

def GateLine (cur : Point f ell) : Prop :=
  ∃ u : exteriorRows (G.selector ell) (G.ready ell) (G.centre ell X.centre) X.group,
    ∃ tail : Trace (firstRetained X u).next cur,∀ p : PortAt cur,
      let M := firstRetained X u
      let first : Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) (T:=T) u.val) M.next :=
        .keep .start M
      let A := actualLane X gate pad (M.back (tail.back p)).val
      A∈(outerLanes X gate pad).result.lanes ∧
        (carryBody tail.depth A.gate.body).result=(concatenate first tail).literal (rootGateBody u.val) p ∧
        A.gate.origin.pageKey=none ∧ A.gate.origin.stamp.created.val=(entry cur).created

def PageLine (cur : Point f ell) : Prop :=
  ∃ k : CanonicalPage m, ∃ tail : Trace (stableBorn X k) cur,
    (locate (widened pad (residentPageKey m k)).result
        (X.seed pad).immutable.payload.payload.pages).result=some (X.chosenFields k) ∧
    ∀ p : PortAt cur,
      let A := actualLane X gate pad (packetRootHalf X k (tail.back p))
      A∈(outerLanes X gate pad).result.lanes ∧
        (carryBody tail.depth A.packet.body).result=tail.literal (originSeed (rootChart T) (oddAxis m) X.group k) p ∧
        A.packet.origin.stamp=(X.seed pad).immutable.payload.stamp ∧
        A.packet.origin.stamp.created.val=(entry cur).created ∧
        A.packet.origin.pageKey=some (widened pad (residentPageKey m k)).result

variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {P : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (born : Births P key prec tw bw (pageKeyWidth m+pad))

theorem actual_path_from_structured_exterior (fits : gate.created.val=base)
    {c : Call (PhysicalHost f ell)} (p : Path sel ext c) (v : c.host.Row⊕c.host.Col) :
    GateLine X gate pad (J6R34ChildPath.point c.host v) ∨
    PageLine X gate pad (J6R34ChildPath.point c.host v) ∨
    (∃ (start : Call (PhysicalHost f ell)) (older : Path sel ext start)
      (w : (Plan sel).Slot start) (k : PageAt P (older.ticket w)),
      OnPath born (born older w).job p ∧
      Nonempty (Trace (bornPoint P (older.ticket w) k) (J6R34ChildPath.point c.host v))) := by
  rcases actual_path_has_typed_origin born p v with h|inner
  · obtain ⟨u,⟨tail⟩⟩ := h
    rcases u with old|packet
    · have eq : (firstRetained X old).next=J6R34ChildPath.point (ext).host (.inl old) :=
        retained_prescribed_point (G.selector ell) (G.ready ell) (G.centre ell X.centre)
          (rootPreset G ell) X.sample X.group old
      let t : Trace (firstRetained X old).next (J6R34ChildPath.point c.host v) := eq.symm ▸ tail
      exact Or.inl ⟨old,t,actual_gate_seed_continues X gate fits pad old t⟩
    · let E := canonicalPageEquiv G ell X.centre
      let k := E.symm packet
      have hp : E k=packet := E.apply_symm_apply packet
      have eq := stable_exterior_exact_born X k
      change exteriorPagePoint (G.selector ell) (G.ready ell) (G.centre ell X.centre)
        (rootPreset G ell) X.sample X.group (E k)=stableBorn X k at eq
      rw [hp] at eq
      have baseEq : J6R34ChildPath.point (ext).host (.inr packet)=stableBorn X k := eq
      let t : Trace (stableBorn X k) (J6R34ChildPath.point c.host v) := baseEq ▸ tail
      exact Or.inr (Or.inl ⟨k,t,true_seed_payload_page X pad k,actual_page_seed_continues X gate pad k t⟩)
  · exact Or.inr (Or.inr inner)

#print axioms actual_path_from_structured_exterior
end J6R37StructuredRoot