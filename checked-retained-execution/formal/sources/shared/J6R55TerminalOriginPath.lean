import J6R55TerminalOriginMachine
import J6R54TerminalBootPath

/-! The old two-field boot interface now needs only the physical-body
receipt for the actually generated input; the origin theorem is internal.
Origins alone also propagate through the same online source recursion,
without imposing any body hypotheses. -/
namespace J6R55TerminalOrigin
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R53OldOwner J6R53OldOwnerRoot J6R54ExteriorOwner J6R41StructuredAllPaths J6R51Online J6R54TerminalBoot
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 33000000
set_option maxRecDepth 6100
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own rate : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)



variable (M : (OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate))
variable (slots : ∀ w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group), LiteralFirstSlot X gate pad root w T)
variable (B : (PageBank f ell key prec tw bw (pageKeyWidth m+pad))) (live : IsLive (X.seed pad) B) (rootInj : Function.Injective rootName)




theorem origin_seam_retains_only_body_receipt
    (bodies : ∀ (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) h,
      ((compileOccurrence (slots w).occurrence.result).native.physical.record h).body=
        (initialPayload X gate pad h).2) :
    ExactPrintedBoot X (withGeneratedOrigins X gate pad root M slots B live rootInj) gate := by
  refine ⟨same_generated_machine_has_literal_origins X gate pad root M slots B live rootInj,?_⟩
  intro w h
  exact bodies w h

theorem same_first_slot_uses_origin_of_written_outer_port
    (gateWidth : gate.created.val=base) (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
    (u : ((exteriorChild G ell X.centre X.sample X.group)).host.Row⊕((exteriorChild G ell X.centre X.sample X.group)).host.Col) (h : PortAt (J6R34ChildPath.point ((exteriorChild G ell X.centre X.sample X.group)).host u)) :
    ((withGeneratedOrigins X gate pad root M slots B live rootInj).initial w).result.origins u=(initialPayload X gate pad h.val).1 :=
  (congrFun (same_generated_machine_has_literal_origins X gate pad root M slots B live rootInj w) u).trans
    (exact_real_root_tag_at_port X gate pad gateWidth u h).symm

theorem every_generated_path_has_same_source_origins :
    ∀ {c : Call (PhysicalHost f ell)} (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c) (u : (Plan sel).Slot c),
      (sourceState (withGeneratedOrigins X gate pad root M slots B live rootInj) p u).origins=
        expectedOrigin (borns (withGeneratedOrigins X gate pad root M slots B live rootInj)) (fun q w=>occurrencePageWord (sourceState (withGeneratedOrigins X gate pad root M slots B live rootInj) q w).input)
          (initialOrigin X gate pad) p := by
  intro c p
  induction p with
  | root =>
    intro w
    exact same_generated_machine_has_literal_origins X gate pad root M slots B live rootInj w
  | step p z ih =>
    intro w
    let prior := sourceState (withGeneratedOrigins X gate pad root M slots B live rootInj) p z
    let next := ((withGeneratedOrigins X gate pad root M slots B live rootInj).demand prior w).result.advance
    refine next.liveOrigins.trans ?_
    funext vtx
    unfold StoredSite.childOrigins
    rw [expectedOrigin]
    cases e : childVertices T (p.ticket z) vtx with
    | inl old =>
      exact congrFun (ih z) old.val
    | inr fresh => rfl

end
#print axioms origin_seam_retains_only_body_receipt
#print axioms every_generated_path_has_same_source_origins
#print axioms same_first_slot_uses_origin_of_written_outer_port
end J6R55TerminalOrigin
