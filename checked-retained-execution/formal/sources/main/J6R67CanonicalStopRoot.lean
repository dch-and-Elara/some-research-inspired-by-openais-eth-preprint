import J6R49LeafRuntime

/-! An actual exterior vertex chooses its source syntax by its physical
constructor, not by elimination of an existential of an extensional row.
Old root gates use their own scope and retained port equivalence; new
root pages use the actual exterior Seed and its canonical page index. -/
namespace J6R67CanonicalStop
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R11 A1R12
open J6Mesh J6OrientedHost P11FullPacking P1DyadicGrid J6R24LegalLayout
open J6R10Repack J6R11Blueprint J6R11Repack J6R12Blueprint J6R21Ancestor J6R20Ancestor
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R26StablePreparedRoot
open J6R14ZeroMode J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R27OriginalGate J6R9PacketScopes
open J6R34RootAtlas J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6R30ProducedGateRegistry J6R22Active J6R35RootOrigins J6R48Leaf J6R49Leaf
open J6R9Recursive J6R10Reachable J6R24MeteredRecursion J6R21Leaf J6R16ModeCost

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13000000
set_option maxRecDepth 4100
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "w₀" => (J6R28GeneratedRootFrame.constantRootWord m)

abbrev rootOldSource (u : (ext).host.Row) : SourceVertex T := u.val

abbrev rootPageSource (k : (ext).host.Col) : CanonicalPage m :=
  (canonicalPageEquiv G ell X.centre).symm k

def oldRootTrace (u : (ext).host.Row) :
    Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) (rootOldSource X u))
      (atVertex ext (.inl u)) :=
  Eq.mp (congrArg (Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) (rootOldSource X u)))
    (retained_prescribed_point (G.selector ell) (G.ready ell) (G.centre ell X.centre)
      (rootPreset G ell) X.sample X.group u))
    (Trace.keep Trace.start
      (retainedFromExterior (G.selector ell) (G.ready ell) (G.centre ell X.centre)
        (rootPreset G ell) X.sample X.group u))

theorem rootPageSource_position (k : (ext).host.Col) :
    atVertex ext (.inr k)=stableBorn X (rootPageSource X k) := by
  let E := canonicalPageEquiv G ell X.centre
  have h := stable_exterior_exact_born X (E.symm k)
  change atVertex ext (.inr (E (E.symm k)))=stableBorn X (E.symm k) at h
  rw [E.apply_symm_apply] at h
  exact h

def pageRootTrace (k : (ext).host.Col) :
    Trace (stableBorn X (rootPageSource X k)) (atVertex ext (.inr k)) :=
  Eq.mp (congrArg (Trace (stableBorn X (rootPageSource X k)))
    (rootPageSource_position X k).symm) Trace.start

variable (pad : ℕ)

def rootRow (basePos : 0<base) (F : Frame f (ext).prec)
    (ord : Fin (ext).edges≃(ext).host.Edge) :
    (v : Vertex ext)→RowAt X.hf F X.positive ord v (IsLive (X.seed pad))
  | .inl u =>
    originalRow T w₀ X.hf F X.positive ord (.inl u) (IsLive (X.seed pad))
      basePos (rootOldSource X u) (oldRootTrace X u)
      (width:=(ext).edges) (Nat.lt_two_pow_self (n:=(ext).edges)).le
  | .inr k =>
    exteriorRow X F X.positive ord (.inr k) pad (rootPageSource X k)
      (IsLive (X.seed pad)) (fun _ h=>h) (pageRootTrace X k)

def rootTape (basePos : 0<base) (F : Frame f (ext).prec)
    (ord : Fin (ext).edges≃(ext).host.Edge) (edgeCount : (ext).host.edgeCount=(ext).edges) :
    RawTape ext key (pageKeyWidth m+pad) :=
  PagedLeaf.toRaw (compiledLeaf edgeCount (rootRow X pad basePos F ord))

theorem actual_root_tape_value (basePos : 0<base) (F : Frame f (ext).prec)
    (ord : Fin (ext).edges≃(ext).host.Edge)
    (edgeCount : (ext).host.edgeCount=(ext).edges)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) (live : IsLive (X.seed pad) B) :
    F.decode (runTape (rootTape X pad basePos F ord edgeCount) X.hf F X.positive B).result=
      reduce (ext).prec f ell ((ext).host.contract X.hf) := by
  let D := compiledLeaf edgeCount (rootRow X pad basePos F ord)
  have same := raw_leaf_is_same_dispatch D X.hf F X.positive B
  exact (congrArg (fun R=>F.decode R.result) same).trans
    (compiled_leaf_in_literal_order edgeCount (rootRow X pad basePos F ord) B live)

#print axioms rootOldSource
#print axioms rootPageSource
#print axioms oldRootTrace
#print axioms rootPageSource_position
#print axioms rootRow
#print axioms actual_root_tape_value
end
end J6R67CanonicalStop

