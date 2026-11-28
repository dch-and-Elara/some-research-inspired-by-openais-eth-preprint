import J6R54TerminalBootLineage
import J6R52TerminalAncestorOrigin

/-! Tie the synchronized body/opcode induction to the actual
sourceState that the online program sends to its real child. There
is no per-path lineage assumption. A native Page cannot acquire an
original Gate opcode along this propagation. -/
namespace J6R54TerminalBoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R21Ancestor J6R15ModeCost
open J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R10Repack J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6ActiveRun J6R32StatefulArithmetic
open J6R50SourceProducer J6R51Online J6R52Terminal J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 34000000
set_option maxRecDepth 5100
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate wCode : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable (M : OnlineMachine T key prec tw bw page rate)
variable (tags : r.host.Row⊕r.host.Col→Origin key prec page)
variable (ports : Port r.host.Edge→Payload key prec page)
variable (rootGates : r.host.Row⊕r.host.Col→Option (CodeGate (Word wCode)))
variable (bootTags : ∀ w,(M.initial w).result.origins=tags)
variable (bootBody : ∀ w h,((M.initial w).result.birth.native.physical.record h).body=(ports h).2)

include bootTags bootBody in
theorem actual_online_gate_and_origin_are_joint
    (boot : ∀ (u : r.host.Row⊕r.host.Col) (h : PortAt (point r.host u)),(ports h.val).1=tags u)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (u : c.host.Row⊕c.host.Col) :
    (∃ A : ExteriorOrigin M tags ports p w u,gateHistory T rootGates p u=rootGates A.vertex) ∨
    (Nonempty (AncestorOrigin M p w u) ∧ gateHistory T rootGates p u=none) := by
  let L := fromOnline M tags ports bootTags bootBody
  let D := buildAlong L p w
  have same : D=sourceState M p w := generated_site_has_no_lineage_table M tags ports bootTags bootBody p w
  have equalBorn : @births f ell s C key prec tw bw page cfg sel r hf T tags ports L =
      @borns f ell s C key prec tw bw page rate cfg sel r hf T M :=
    exact_actual_online_births M tags ports bootTags bootBody
  let linked := online_paths_have_no_supplied_link_table L
  have lines := linked_paths_carry_gate_and_body_together rootGates (files L) ports linked boot p u
  have different (q : Port c.host.Edge) :
      ((sourceState M p w).birth.native.physical.record q).body=(publishedPayload (files L) ports p q).2 := by
    rw [← same]
    exact linked.copiedBody p w q
  have tag : (sourceState M p w).origins u=expectedOrigin (births L) (pageKeys L) tags p u := by
    rw [← same]
    exact congrFun (built_origin_table_is_the_actual_path L p w) u
  rcases lines with exterior|native
  · obtain ⟨root,trace,⟨actualTag,bodies⟩,sameGate⟩ := exterior
    refine Or.inl ⟨⟨root,trace,tag.trans actualTag,
      fun q=>(different q.val).trans (congrArg Prod.snd (bodies q))⟩,sameGate⟩
  · obtain ⟨inside,noneGate⟩ := native
    obtain ⟨home,atHome,slot,k,named,trace,actualTag,bodies⟩ := inside
    have own : OnPath (borns M) (borns M atHome slot).job p := by
      rw [← equalBorn]
      exact named
    have wordAt : (files L atHome slot).pageKey k =
        J6R49SourceLayout.occurrencePageWord (sourceState M atHome slot).input k := by
      refine (congrFun (linked.canonicalPages atHome slot) k).trans ?_
      unfold pageKeys
      rw [generated_site_has_no_lineage_table M tags ports bootTags bootBody atHome slot]
    have stamp :
        nativeOrigin (files L atHome slot) k =
          ⟨(borns M atHome slot).job.immutable.payload.stamp,
          some (J6R49SourceLayout.occurrencePageWord (sourceState M atHome slot).input k)⟩ := by
      unfold nativeOrigin
      rw [← equalBorn,wordAt]
    exact Or.inr ⟨⟨⟨home,atHome,slot,k,own,trace,(tag.trans actualTag).trans stamp,
      fun q=>(different q.val).trans (congrArg Prod.snd (bodies q))⟩⟩,noneGate⟩

end
#print axioms actual_online_gate_and_origin_are_joint
end J6R54TerminalBoot
