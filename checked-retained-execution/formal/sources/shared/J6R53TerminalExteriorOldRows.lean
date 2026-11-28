import J6R53TerminalGateSource
import J6R53TerminalExteriorPage
import J6R53TerminalGateOwner
import J6R52TerminalNativeDispatch

/-! Three genuine retained source routes share one metered owner
interpreter. Only a typed source provenance proof is needed; there is
no supplied command tape or supplied value law. -/
namespace J6R53TerminalExterior
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R50Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 43000000
set_option maxRecDepth 5700
set_option Elab.async false

theorem no_command_choice_by_bits {A B C : Type} (initial : B)
    (out : Option A) (value : A→B→C) (target : B→C)
    (all : ∀ z,∃ cmd,out=some cmd ∧ value cmd z=target z) :
    ∃ cmd,out=some cmd ∧ ∀ z,value cmd z=target z := by
  obtain ⟨cmd,eq,_⟩ := all initial
  refine ⟨cmd,eq,fun z=>?_⟩
  obtain ⟨c,h,good⟩ := all z
  have e := Option.some.inj (eq.symm.trans h)
  exact e.symm ▸ good

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)

inductive KnownOldOrigin (u : OldAt T (p.ticket w)) (gate : Option (CodeGate (Word (pageKeyWidth m+a m)))) : Prop
  | original (x : SourceVertex P)
    (tr : Trace (stableOriginal (f:=f) (ell:=ell) (base:=base) x) (J6R34ChildPath.point c.host u.val))
    (body : ∀ a : PortAt (J6R34ChildPath.point c.host u.val),
      ((sourceState M p w).birth.native.physical.record a.val).body=tr.literal (rootGateBody x) a)
    (code : gate=some (encodeGate (rootSuffixAt (f:=f) (ell:=ell) (base:=base) P x∘
      (originalPortGate P (J6R28GeneratedRootFrame.constantRootWord m) x).port)
      (originalPortGate P (J6R28GeneratedRootFrame.constantRootWord m) x).gate)) :
    KnownOldOrigin u gate
  | exterior (k : CanonicalPage m)
    (tr : Trace (stableBorn X k) (J6R34ChildPath.point c.host u.val))
    (tag : (sourceState M p w).origins u.val=⟨(X.seed pad).immutable.payload.stamp,
      some (widened pad (residentPageKey m k)).result⟩)
    (body : ∀ a : PortAt (J6R34ChildPath.point c.host u.val),
      ((sourceState M p w).birth.native.physical.record a.val).body=
          tr.literal (originSeed (rootChart P) (oddAxis m) X.group k) a)
    (noGate : gate=none) : KnownOldOrigin u gate
  | native (A : AncestorOrigin M p w u.val)
    (noGate : gate=none) : KnownOldOrigin u gate

theorem actual_old_origin_compiles_and_evaluates
    (old : (p.ticket w).child.host.Row)
    (gate : Option (CodeGate (Word (pageKeyWidth m+a m))))
    (provenance : KnownOldOrigin X M p w (physicalChildRows (T:=T) (v:=p.ticket w) old) gate)
    (saved : CachedParentFrames (sourceState M p w).site)
    (inj : Function.Injective (sourceState M p w).site.oldKey)
    (hBase : 0<base) {b : ℕ} (hb : 0<b) (fit : (p.ticket w).child.edges≤2^b)
    (rootLive : PageBank f ell key prec tw bw (pageKeyWidth m+pad)→Prop)
    (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (openRoot : IsLive (X.seed pad) B)
    (live : opened (borns M) rootLive p B)
    (F : Frame f (p.ticket w).child.prec) :
    let v := p.ticket w
    let site := sourceState M p w
    let u := physicalChildRows (T:=T) (v:=v) old
    let op := compileByOwnerData b (cachedBook site saved).result saved.rows (site.site.oldKey u.val)
      ⟨site.origins u.val,gate⟩
    let ord := actualEdgeOrder T v site.birth.native.physical
    ∃ cmd,op.result=some cmd ∧ ∀ bits : Fin v.child.edges→Bool,
      F.decode ((cmd : ReadCmd key (pageKeyWidth m+pad)).read X.hf F T.vPositive B (List.ofFn bits)).result =
        (v.child.host.file (.inl old)).read X.hf v.child.prec (assignment v.child.host.network
          (bits∘ord.symm) (.inl old)) := by
  let v := p.ticket w
  let site := sourceState M p w
  let u := physicalChildRows (T:=T) (v:=v) old
  let ord := actualEdgeOrder T v site.birth.native.physical
  let op := compileByOwnerData b (cachedBook site saved).result saved.rows (site.site.oldKey u.val)
      ⟨site.origins u.val,gate⟩
  apply no_command_choice_by_bits (fun _ : Fin v.child.edges=>false) op.result
  intro bits
  have transport := literal_row_value_transport (p:=v.child.prec) X.hf v.child.host
    (literalHost T v) (actual_ticket_host T v) old ord bits
  cases provenance with
  | original x tr body code =>
    obtain ⟨cmd,paid,read⟩ := actual_cached_original_gate_read P hBase hb fit site saved inj u
      x tr body F B bits
    refine ⟨cmd,?_,read.trans transport⟩
    unfold op compileByOwnerData
    dsimp only
    rw [code]
    exact paid
  | exterior k tr tag body noneGate =>
    obtain ⟨cmd,paid,read⟩ := actual_cached_exterior_page_read X site saved inj u k tr tag body B openRoot F bits
    refine ⟨cmd,?_,read.trans transport⟩
    unfold op compileByOwnerData
    dsimp only
    rw [noneGate]
    exact paid
  | native A noneGate =>
    obtain ⟨cmd,paid,read⟩ := actual_compiled_native_ancestor_page M p w u A saved inj rootLive B live F bits
    refine ⟨cmd,?_,read.trans transport⟩
    unfold op compileByOwnerData
    dsimp only
    rw [noneGate]
    exact paid

end
#print axioms no_command_choice_by_bits
#print axioms actual_old_origin_compiles_and_evaluates
end J6R53TerminalExterior
