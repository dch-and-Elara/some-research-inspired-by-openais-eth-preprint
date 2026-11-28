import J6R49LiveCanonicalRun
import J6R49LeafRuntime

/-! Attach the new actual typed stopping leaf to the same streaming
recursion. Leaf source values are conclusions, not constructor inputs.
The typed input family and its layout/route data remain premises. -/
namespace J6R49LiveBits
open scoped Polynomial
open J6Mesh J6OrientedHost J6R21Ancestor J6R32RootGeneratedRegistryInputs J6R31RootResidentTables
open J6R34RootAtlas J6R35RootOrigins J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26StablePreparedRoot J6R24MeteredRecursion J6R48DFS J6R49DFS J6R49Leaf
open J6R30GeneratedRootLayout J6R27OriginalGate J6R24LegalLayout J6R10Repack

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 3200

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw s C streamQ : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (pad : ℕ)
variable (I : InputFamily T key prec tw bw (pageKeyWidth m+pad))

variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

noncomputable def literalLeafStreaming (basePos : 0<base) (hq : 0<streamQ)
    (ord : ∀ {c : Call (PhysicalHost f ell)}, Path sel (exteriorChild G ell X.centre X.sample X.group) c → Fin c.edges ≃ c.host.Edge)
    (A : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (h : ((printedParams (f:=f) (ell:=ell) s)).cutoff<c.edges),
      ActiveMachine sel (ready_reachable cfg sel p.reached T.rootStable h) T.bank streamQ) :
    StreamingResident T key prec tw bw (pageKeyWidth m+pad) streamQ where
  modeWidth := hq
  births := compileFamily I
  rootLive := IsLive (X.seed pad)
  rootStable := live_monotone (X.seed pad)
  leaf p stop B := literalLeafExec X pad I basePos p stop (ord p) B
  leafMatches p stop B h :=
    (literal_leaf_exec_correct X pad I basePos p stop (ord p) B h).trans
      (T.correctAt _ p.reached).symm
  active := A

theorem original_stream_with_literal_stopping_words (basePos : 0<base) (hq : 0<streamQ)
    (ord : ∀ {c : Call (PhysicalHost f ell)}, Path sel (exteriorChild G ell X.centre X.sample X.group) c → Fin c.edges ≃ c.host.Edge)
    (A : ∀ {c : Call (PhysicalHost f ell)} (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (h : ((printedParams (f:=f) (ell:=ell) s)).cutoff<c.edges),
      ActiveMachine sel (ready_reachable cfg sel p.reached T.rootStable h) T.bank streamQ)
    (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad) → ℕ)
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (origin : IsLive (X.seed pad) initial)
    (valid : ReadyOnStack (compileFamily I) initial) :
    let run := nativeStream
      (canonicalStreaming (literalLeafStreaming X pad I basePos hq ord A)) retire (exteriorChild G ell X.centre X.sample X.group) .root initial
    (T.frame (NativeReach.reflexive (exteriorChild G ell X.centre X.sample X.group))).decode run.result.1 =
        (sourceBlueprint sel (exteriorChild G ell X.centre X.sample X.group) X.hf).program.run (exteriorChild G ell X.centre X.sample X.group) ∧
      run.result.2=initial :=
  canonical_whole_stream (literalLeafStreaming X pad I basePos hq ord A) retire initial origin valid

#print axioms literalLeafStreaming
#print axioms original_stream_with_literal_stopping_words
end J6R49LiveBits

