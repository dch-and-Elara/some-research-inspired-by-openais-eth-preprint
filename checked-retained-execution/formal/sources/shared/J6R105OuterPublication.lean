import J6R75OuterTimeBill

/-! Exact fee of the actual outer publication. This isolates the
stored header bytes and the paid atlas compilation; equality of
published values is not used to exchange costs. -/
namespace J6R105OuterPublication
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R34RootAtlas J6R35GatewayPreparation
open J6R33PageIndexedBirth J6R32ChildResidentTransfer
open J6R57PublicRequest J6R75OuterTime J6R32RootGeneratedRegistryInputs
open P11FullPacking J6Mesh J6OrientedHost J6R24LegalLayout J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R31RootResidentTables

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4300
set_option maxHeartbeats 15000000

def storedHeaderBits {key : ℕ} (headers : List (DirRow key)) : ℕ :=
  (headers.map (fun r => r.bytes.length)).sum

theorem directory_fetch_uses_all_old_header_bytes {key : ℕ} (headers : List (DirRow key)) :
    fetchFee headers=2+(12*key+12)*headers.length+3*storedHeaderBits headers := by
  induction headers with
  | nil => simp [fetchFee, storedHeaderBits]
  | cons h xs ih =>
    simp only [fetchFee, ih, rowFee, storedHeaderBits, List.map_cons, List.sum_cons,
      List.length_cons]
    ring

def headerBill (key prec tw bw offset hcount rcount oldBits newBits : ℕ) : ℕ :=
  (12*key+12)*hcount+(13*key+13)*rcount+
    3*oldBits+6*newBits+18*key+7*prec+3*tw+3*bw+3*offset+70

theorem publication_keeps_its_install_and_atlas_cost {key prec tw bw : ℕ} {D : Type*}
    (B : Ledger key prec tw bw D) (E : Meter (DirRow key)) (offset : ℕ)
    (built : Meter (Option D)) :
    publishFee B E offset built=E.steps+built.steps+
      headerBill key prec tw bw offset B.headers.length B.records.length
        (storedHeaderBits B.headers) E.result.bytes.length := by
  rw [publishFee, installFee, directory_fetch_uses_all_old_header_bytes]
  unfold headerBill rowFee locateFee headerReadFee contextCopyFee
  ring

theorem explicit_root_table_page_count {m p ell q : ℕ} {i : Fin (a m)}
    {fw : List (A1R10.Word p)}
    (fields : Page (a m) (K m) (Fin 64) → OriginFields (a m) p ell q fw i) :
    (rootTable fields).length=pagesCount (a m) (K m) := by
  unfold rootTable pagesCount
  rw [List.length_map, (child_pages_complete (a m) (K m)).2.2]

theorem root_job_atlas_bill {f : ℤ[X]} {ell key prec tw bw width : ℕ}
    (S : FrameShape f prec) (E : Meter (DirRow key)) (offset : ℕ)
    (ctx : CentreContext tw bw)
    (tag : loadAt prec offset E.result.bytes=⟨some S.birth,headerReadFee prec offset⟩)
    (pad : ℕ) (A : Meter (Option (PageRows S ell width))) (rows : PageRows S ell width)
    (made : A.result=some rows) :
    (rootJob S E offset ctx tag pad A rows made).built.steps=
      A.steps+rows.length*(wideningFee width pad+7)+6+shapeFrameFee prec := by
  change (packPages S (widenAtlas pad A)).steps=_
  rw [packed_pages_exact S (widenAtlas pad A) _ (congrArg Meter.result
    (widen_atlas_exact pad A rows made)), widen_atlas_exact pad A rows made]
  dsimp only
  omega

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]}
variable {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd edgew tc tj key prec tw bw : ℕ}

theorem actual_prepared_publication_counts_each_page_and_header
    (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
    (S : ActualRootPreparation G ell q) (aligned : S=(rootPreparationFor X).result)
    (pad : ℕ) (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :
    let J := preparedSeed X S aligned pad
    let E := headerUsingShared X S
    publishFee B J.entry J.offset J.built=
      E.steps+(readyAtlas X S aligned).steps+
      pagesCount (a m) (K m)*(wideningFee (pageKeyWidth m) pad+7)+6+shapeFrameFee prec+
      headerBill key prec tw bw (externalAddrWidth tc tj 0) B.headers.length B.records.length
        (storedHeaderBits B.headers) E.result.bytes.length := by
  let E := headerUsingShared X S
  let A := readyAtlas X S aligned
  let J := preparedSeed X S aligned pad
  have made : A.result=some (rootTable X.chosenFields) := by
    change (readyAtlas X S aligned).result=_
    rw [ready_atlas_is_literal X S aligned]
    exact (Classical.choose_spec (stable_exterior_atlas X)).1
  have bill : J.built.steps=
      A.steps+pagesCount (a m) (K m)*(wideningFee (pageKeyWidth m) pad+7)+6+shapeFrameFee prec := by
    change (packPages X.frame (widenAtlas pad A)).steps=_
    rw [packed_pages_exact X.frame (widenAtlas pad A) _ (congrArg Meter.result
      (widen_atlas_exact pad A (rootTable X.chosenFields) made)),
      widen_atlas_exact pad A (rootTable X.chosenFields) made]
    dsimp only
    rw [explicit_root_table_page_count]
    omega
  change publishFee B E (externalAddrWidth tc tj 0) J.built=_
  rw [publication_keeps_its_install_and_atlas_cost, bill]
  simp only [E, A, Nat.add_assoc]

#print axioms actual_prepared_publication_counts_each_page_and_header
end
#print axioms directory_fetch_uses_all_old_header_bytes
#print axioms publication_keeps_its_install_and_atlas_cost
#print axioms explicit_root_table_page_count
#print axioms root_job_atlas_bill
end J6R105OuterPublication
