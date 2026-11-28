import J6R114RetainedScopeTariffBase
import J6R114RetainedScopeTariffLists

/-! An explicit polynomial in the true uniform vertex envelope and
real bit widths, not a new upper bound on an arbitrary Meter. -/
namespace J6R114RetainedScopeTariff
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R82LayoutDebit V8NativeMessage.N2DLabels
open J6R111KeptOwnerFlow J6R55CachedLedger J6R53PeakAddon J6R49Cost
open J6R48GeneratedAddons J6R68.RecursivePeak J6R52CacheSource J6R57ScopeFee
open J6R62Leaf J6R58LeafScale J6R26DescriptorTree J6R57PublicRequest J6R21Leaf
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
set_option maxRecDepth 5450
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
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
variable (A : CapturedEntry X p w Y)
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (u : (Plan sel).Slot (p.ticket w).child)
variable (H : ParentOwnerHeaders Y.site)

def keptOwnerScanRoof (own page code key prec arity V₀ : ℕ) : ℕ :=
  2*(7+(6*own+78)*V₀) +
  2*(7+(3*page+7)*V₀) +
  (10+V₀*(4*(own+page)+6*(1+(own+page))+14)) +
  (3+V₀*(locateFee own V₀+ownerDataCap code key prec page arity+8)) +
  (3+V₀*(ownerDataCap code key prec page arity+4)) +
  (4*V₀+3) + (3*(1+(own+page))+6)*V₀ + 26

theorem actual_kept_owner_scan_is_bounded_by_its_vertex_and_word_polynomial
    (arity : ℕ) (gateFit : observedGateWidth A.owners.raw≤arity) :
    let V₀ := vertexCount (exteriorChild G ell X.centre X.sample X.group).host+4*(C*s)
    keptSuccessorOwnerScan X p w Y A H ≤
      keptOwnerScanRoof Y.site.ownerWidth (pageKeyWidth m+pad) (pageKeyWidth m+J6Mesh.a m) key prec arity V₀ := by
  let V₀ := vertexCount (exteriorChild G ell X.centre X.sample X.group).host+4*(C*s)
  let pg := pageKeyWidth m+pad
  let ow := Y.site.ownerWidth
  let code := pageKeyWidth m+J6Mesh.a m
  let gh := gateHistory T (bootGates X) p
  let O := readOldVertices Y.site H
  let U := vertexKeysOfBirth Y.site O.result Y.canonical
  let tagged := tagOwnerWords U.result.rawRows U.result.rawCols
  let data := bornOwnerData Y gh A.owners H
  let sought := gatherOwners A.owners.raw U.result.rawRows
  let fresh := writeFreshOwners (gate:=code) Y.birth.job.immutable.payload.stamp U.result.rawCols
  let unit := ownerDataCap code key prec pg arity
  have hp : vertexCount c.host≤V₀ := (actual_leaf_field_width_and_vertices (T:=T) p).2.2
  have hc : vertexCount (p.ticket w).child.host≤V₀ :=
    (actual_leaf_field_width_and_vertices (T:=T) (Path.step p w)).2.2
  have Hlen : H.raw.length≤V₀ := (all_actual_grouped_headers_count_the_parent_vertices X p w Y H).trans_le hp
  have Alen : A.owners.raw.length≤V₀ := by
    rw [A.owners.exactRows,List.length_map]
    exact (complete_vertex_list_length c.host A.owners.order A.owners.unique A.owners.complete).trans_le hp
  have full : (bornOwnerOrder Y H).length≤V₀ :=
    (complete_vertex_list_length (p.ticket w).child.host (bornOwnerOrder Y H)
      (born_owner_order_full Y H).1 (born_owner_order_full Y H).2).trans_le hc
  have sum : U.result.rawRows.length+U.result.rawCols.length=(bornOwnerOrder Y H).length := by
    rw [U.result.exactRows,U.result.exactCols,List.length_map,List.length_map]
    change _=(U.result.order Y.site).length
    simp only [VertexKeys.order,List.length_append,List.length_map]
  have rowN : U.result.rows.length≤V₀ := by
    have n : U.result.rawRows.length=U.result.rows.length := by rw [U.result.exactRows,List.length_map]
    omega
  have oldN : O.result.rows.length≤V₀ := rowN
  have rowWords : U.result.rawRows.length≤V₀ := by omega
  have freshWords : U.result.rawCols.length≤V₀ := by omega
  have rootRows : Y.birth.rows.length≤V₀ := by
    have h := (actual_occurrence_compact_chart p w Y.input).1
    have pow : 0<(2:ℕ)^((printedParams (f:=f) (ell:=ell) s).levelBits c.depth) := by positivity
    change Y.birth.rows.length*2^((printedParams (f:=f) (ell:=ell) s).levelBits c.depth)≤3*(C*s) at h
    have n := (Nat.le_mul_of_pos_right Y.birth.rows.length pow).trans h
    dsimp only [V₀]
    omega
  have bOld : O.steps≤7+(6*ow+78)*V₀ := by
    have a := (exact_old_vertices_from_grouped_headers Y.site H).2
    change O.steps=7+(3*ow+77)*H.raw.length+(3*ow+1)*O.result.rows.length at a
    rw [a,show 6*ow+78=(3*ow+77)+(3*ow+1) by omega,
      Nat.add_mul (3*ow+77) (3*ow+1) V₀]
    simpa only [Nat.add_assoc] using
      Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left (3*ow+77) Hlen) 7)
        (Nat.mul_le_mul_left (3*ow+1) oldN)
  have bAtlas : U.steps≤7+(3*pg+7)*V₀ := by
    have a := (exact_vertex_roster_from_actual_birth Y.site O.result Y.canonical).2.2.2
    change U.steps=7+(3*pg+7)*Y.birth.rows.length at a
    rw [a]
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ rootRows) _
  have bTags : tagged.steps≤10+V₀*(4*(ow+pg)+6*(1+(ow+pg))+14) :=
    (actual_tagged_owner_copy_cap U.result.rawRows U.result.rawCols).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ (sum.trans_le full)) _)
  have bRead : sought.steps≤3+V₀*(locateFee ow V₀+unit+8) := by
    have price := actual_owner_lookup_scan_cap A.owners.raw arity
      (fun row h g known=>let fit := gate_width_is_observed A.owners.raw row h g known
        ⟨fit.1.trans gateFit,fit.2.trans gateFit⟩) U.result.rawRows
    have kw := locate_fee_mono_width_tables (k:=ow) (K:=ow) le_rfl Alen
    exact price.trans (Nat.add_le_add_left
      (Nat.mul_le_mul rowWords (Nat.add_le_add_right (Nat.add_le_add_right kw _) _)) _)
  have bFresh : fresh.steps≤3+V₀*(unit+4) :=
    (actual_born_owner_copy_cap (gate:=code) Y.birth.job.immutable.payload.stamp U.result.rawCols arity).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ freshWords) _)
  have charge := actual_owner_scan_exact_separate_subcharges X p w Y A H
  have name : (actualOwnerNameTape Y H).steps=O.steps+U.steps+tagged.steps+4 := rfl
  have datum : data.steps=O.steps+U.steps+sought.steps+fresh.steps+(4*U.result.rows.length+3)+7 :=
    congrArg Meter.steps (born_owner_data_actual Y gh A.owners H A.labelled.names)
  change keptSuccessorOwnerScan X p w Y A H≤keptOwnerScanRoof ow pg code key prec arity V₀
  change keptSuccessorOwnerScan X p w Y A H=(actualOwnerNameTape Y H).steps+data.steps+
    (3*(1+(ow+pg))+6)*(bornOwnerOrder Y H).length+15 at charge
  rw [charge,name,datum]
  have stitch := Nat.add_le_add_right (Nat.mul_le_mul_left 4 rowN) 3
  have rekey := Nat.mul_le_mul_left (3*(1+(ow+pg))+6) full
  unfold keptOwnerScanRoof
  rw [Nat.two_mul,Nat.two_mul]
  change _≤_+_+_+(3+V₀*(locateFee ow V₀+unit+8))+(3+V₀*(unit+4))+
    (4*V₀+3)+(3*(1+(ow+pg))+6)*V₀+26
  omega

#print axioms actual_kept_owner_scan_is_bounded_by_its_vertex_and_word_polynomial
end
end J6R114RetainedScopeTariff
