import J6R35RootOriginsChain
import J6R35RootOriginsStable
import J6R34ChildPathOrigins
import J6R34RootAtlasLive

/-! Follow an actual exterior invocation and *all* subsequent native
moves, without resetting the depth or conflating a physical Page with
its position. The classification is pure; paid raw leaf routes still
need a physically serialized address proof. -/
namespace J6R35RootOrigins
open scoped Polynomial
open Polynomial J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout
open J6R10Repack J6R11Blueprint J6R12Blueprint J6R21Ancestor
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R26StablePreparedRoot
open J6R14ZeroMode J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R31RootResidentTables
open J6R24MeteredRecursion J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R16ModeCost
set_option autoImplicit false
set_option maxHeartbeats 19000000
set_option maxRecDepth 2700

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw s C : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {P : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (pad : ℕ)
local notation "child" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Q" => (pageKeyWidth m+pad)
variable (born : Births P key prec tw bw (pageKeyWidth m+pad))

/-- Each endpoint comes from one source Gate, one true Page of the
single exterior call, or an earlier live native occurrence on the
same call path. The exterior branch carries the actual seed lookup
law, not witness-provided numerical coefficients. -/
def FullTypedOrigin {c : Call (PhysicalHost f ell)} (p : Path sel child c) (cur : Point f ell) : Prop :=
  (∃ u : SourceVertex T,Nonempty (Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) u) cur)) ∨
  (∃ k : CanonicalPage m,
    (locate (widened pad (residentPageKey m k)).result
      (X.seed pad).immutable.payload.payload.pages).result=some (X.chosenFields k) ∧
    Nonempty (Trace (stableBorn X k) cur)) ∨
  (∃ (start : Call (PhysicalHost f ell)) (older : Path sel child start)
      (w : (Plan sel).Slot start) (k : J6R34ChildPath.PageAt P (older.ticket w)),
    OnPath born (born older w).job p ∧
    Nonempty (Trace (J6R34ChildPath.bornPoint P (older.ticket w) k) cur))

theorem actual_path_has_full_typed_origin {c : Call (PhysicalHost f ell)}
    (p : Path sel child c) (v : c.host.Row⊕c.host.Col) :
    FullTypedOrigin X pad born p (point c.host v) := by
  rcases J6R34ChildPath.actual_path_has_typed_origin born p v with ext|inner
  · obtain ⟨u,⟨tail⟩⟩ := ext
    rcases stable_exterior_vertex_origin X u with h|h
    · obtain ⟨x,⟨head⟩⟩ := h
      exact Or.inl ⟨x,⟨concatenate head tail⟩⟩
    · obtain ⟨k,⟨head⟩⟩ := h
      exact Or.inr (Or.inl ⟨k,true_seed_payload_page X pad k,⟨concatenate head tail⟩⟩)
  · exact Or.inr (Or.inr inner)

theorem opened_keeps_root {c : Call (PhysicalHost f ell)}
    (p : Path sel child c) (B : PageBank f ell key prec tw bw Q)
    (live : opened born (IsLive (X.seed pad)) p B) :
    IsLive (X.seed pad) B := by
  induction p with
  | root => exact live
  | step par w ih => exact ih live.1

theorem actual_path_has_full_live_origin {c : Call (PhysicalHost f ell)}
    (p : Path sel child c) (v : c.host.Row⊕c.host.Col)
    (B : PageBank f ell key prec tw bw Q) (running : opened born (IsLive (X.seed pad)) p B) :
    (∃ u : SourceVertex T, Nonempty (Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) u) (point c.host v))) ∨
    (∃ k : CanonicalPage m, IsLive (X.seed pad) B ∧
      (locate (widened pad (residentPageKey m k)).result
        (X.seed pad).immutable.payload.payload.pages).result=some (X.chosenFields k) ∧
      Nonempty (Trace (stableBorn X k) (point c.host v))) ∨
    (∃ (start : Call (PhysicalHost f ell)) (older : Path sel child start)
      (w : (Plan sel).Slot start) (k : J6R34ChildPath.PageAt P (older.ticket w)),
      IsLive (born older w).job B ∧
      Nonempty (Trace (J6R34ChildPath.bornPoint P (older.ticket w) k) (point c.host v))) := by
  rcases actual_path_has_full_typed_origin X pad born p v with original|outer|inner
  · exact Or.inl original
  · obtain ⟨k,lookup,tr⟩ := outer
    have rootLive := opened_keeps_root X pad born p B running
    exact Or.inr (Or.inl ⟨k,rootLive,lookup,tr⟩)
  · obtain ⟨start,older,w,k,h,tr⟩ := inner
    exact Or.inr (Or.inr ⟨start,older,w,k,ancestor_paged_live born _ p h B running,tr⟩)

end J6R35RootOrigins
#print axioms J6R35RootOrigins.actual_path_has_full_typed_origin
#print axioms J6R35RootOrigins.actual_path_has_full_live_origin
