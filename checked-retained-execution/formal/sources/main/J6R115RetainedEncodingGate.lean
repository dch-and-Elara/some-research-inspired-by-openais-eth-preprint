import J6R111KeptOwnerFlowStop
import J6R68CanonicalRootWriterRateGeometry
import J6R51PeakSidecar

/-! The actual retained owner tape carries original gate syntax and fixed
typed Origin words. There is no arbitrary decoded certificate of shape. -/
namespace J6R115RetainedEncoding
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
open J6R52CacheWhole J6R51ParentFrames J6R82LayoutDebit J6R82LeafTime
open J6R9Recursive J6R58LeafScale J6R16ModeCost J6R14LayoutCost J6R68ActiveInputs
open V8NativeMessage.N2DLabels J6R10Repack J6R94HeldOwnerProvider J6R110ScopeWordRates
open J6R30ProducedGateRegistry J6R66Active J6R64Active J6R68.RecursivePeak J6R54PeakInput J6R59Public
open J6R51ParentFrames J6R65LeafRate J6R82LeafTime J6R24MeteredRecursion
open J6R111KeptOwnerFlow J6R58BootScope J6R68CanonicalRootWriter J6R51Peak
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 28000000
set_option maxRecDepth 5500
set_option Elab.async false

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
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)

theorem observed_max_bound_of_real_rows {A : Type*} (f₀ : A→ℕ) (rows : List A) (roof : ℕ)
    (fit : ∀ x∈rows,f₀ x≤roof) : observedMax f₀ rows≤roof := by
  induction rows with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    exact max_le (fit x List.mem_cons_self) (ih (fun y hy=>fit y (List.mem_cons_of_mem _ hy)))

theorem every_plant_gate_has_at_most_its_true_wire_count
    {V₀ : Type*} {m₀ n₀ : ℕ} (B : Plant V₀ m₀ n₀) (v : V₀) :
    B.degree v≤m₀ := by
  let i : Fin (B.degree v)→Fin m₀ := fun b=>B.rowPort ⟨v,b⟩
  have hinj : Function.Injective i := by
    intro a b eq
    exact eq_of_heq (Sigma.mk.inj_iff.mp (B.rowPort.injective eq)).2
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective i hinj

theorem actual_boot_gates_fit_their_original_arity (d : ℕ) (deg : ∀ v,P.degree v≤d)
    (u : (exteriorChild G ell X.centre X.sample X.group).host.Row⊕
      (exteriorChild G ell X.centre X.sample X.group).host.Col)
    (g : CodeGate (Word (pageKeyWidth m+J6Mesh.a m))) (hit : bootGates X u=some g) :
    GateFit (max d 2) g := by
  cases u with
  | inl x =>
    have eq : printedGateCode (f:=f) (ell:=ell) (base:=base) P x.val=g := Option.some.inj hit
    rw [←eq]
    exact encoded_gate_operand_shape (original_root_local_gate_fits d deg x.val) _ _
  | inr x => contradiction

theorem actual_retained_gate_history_has_original_arity (d : ℕ) (deg : ∀ v,P.degree v≤d) :
    ∀ (u : c.host.Row⊕c.host.Col) (g : CodeGate (Word (pageKeyWidth m+J6Mesh.a m))),
      gateHistory T (bootGates X) p u=some g → GateFit (max d 2) g := by
  induction p with
  | root => exact actual_boot_gates_fit_their_original_arity X d deg
  | @step k path slot ih =>
    intro u g found
    cases here : childVertices T (path.ticket slot) u with
    | inl old =>
      apply ih old.val g
      rwa [gate_history_keeps (rootGates:=bootGates X) path slot u old here] at found
    | inr fresh =>
      rw [gate_history_fresh (rootGates:=bootGates X) path slot u fresh here] at found
      contradiction

variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
variable (A : CapturedEntry X p w Y)

theorem actual_captured_owner_codes_fit_source_arity (d : ℕ) (deg : ∀ v,P.degree v≤d) :
    observedGateWidth A.owners.raw≤max d 2 := by
  unfold observedGateWidth
  apply observed_max_bound_of_real_rows
  intro row used
  rw [A.owners.exactRows] at used
  obtain ⟨v,_,eq⟩ := List.mem_map.mp used
  subst row
  cases h : gateHistory T (bootGates X) p v with
  | none => simpa only [parentData,h] using (Nat.zero_le (max d 2))
  | some g =>
    obtain ⟨q,r⟩ := actual_retained_gate_history_has_original_arity X p d deg v g h
    simpa only [parentData,h] using (max_le q r)

theorem actual_captured_gate_scan_needs_at_most_the_wire_count :
    observedGateWidth A.owners.raw≤max m 2 :=
  actual_captured_owner_codes_fit_source_arity X p w Y A m
    (every_plant_gate_has_at_most_its_true_wire_count P)

theorem actual_observed_retained_origin_has_fixed_wire_width
    (row : RefRow Y.site.ownerWidth (OwnerData (pageKeyWidth m+J6Mesh.a m) key prec (pageKeyWidth m+pad))) :
    (originWords row.payload.origin).length≤key+prec+1+(pageKeyWidth m+pad) := by
  rw [origin_words_exact]
  split <;> omega

theorem actual_captured_roster_payload_cap_from_source_arity
    (d : ℕ) (deg : ∀ v,P.degree v≤d) :
    ∀ row∈A.owners.raw, ownerDataFee row.payload≤
      ownerDataCap (pageKeyWidth m+J6Mesh.a m) key prec (pageKeyWidth m+pad) (max d 2) := by
  intro row used
  apply actual_gate_roster_payload_cap
  intro g got
  obtain ⟨l,r⟩ := gate_width_is_observed A.owners.raw row used g got
  have cap := actual_captured_owner_codes_fit_source_arity X p w Y A d deg
  exact ⟨l.trans cap,r.trans cap⟩

#print axioms observed_max_bound_of_real_rows
#print axioms every_plant_gate_has_at_most_its_true_wire_count
#print axioms actual_retained_gate_history_has_original_arity
#print axioms actual_captured_owner_codes_fit_source_arity
#print axioms actual_captured_gate_scan_needs_at_most_the_wire_count
#print axioms actual_observed_retained_origin_has_fixed_wire_width
#print axioms actual_captured_roster_payload_cap_from_source_arity
end
end J6R115RetainedEncoding
