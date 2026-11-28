import J6R35GatewayPreparationRender

/-! A local seed may be produced from the actually stored root files.
It installs the same immutable bytes as the frozen R34 seed. Its
input preparation was paid outside this local installation; no
descendant route or execution order is transported here. -/
namespace J6R35GatewayPreparation
open scoped Classical Polynomial
open Polynomial AOracleMachineTime
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R30GeneratedRootLayout J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R15ModeCost
open J6R25PreparedSupply J6R17ModeTape J6R27OriginalGate J6R18ChildWrite
open J6R34RootAtlas J6R33PageIndexedBirth J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R21Ancestor
set_option maxHeartbeats 15000000
set_option maxRecDepth 2450
set_option linter.unusedSectionVars false

def alignPages {a p ell q page : ℕ} {i : Fin a}
    {fw old : List (A1R10.Word p)} (same : fw=old)
    (B : Meter (Option (List (PageRow a p ell q page fw i)))) :
    Meter (Option (List (PageRow a p ell q page old i))) :=
  same ▸ B

section Root
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q rr cc dd edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q rr cc dd edgew tc tj key prec tw bw)
variable (S : ActualRootPreparation G ell q)
variable (literal : S=(rootPreparationFor X).result)

noncomputable def readyAtlas : Meter (Option (PageRows X.frame ell (pageKeyWidth m))) :=
  alignPages (congrArg (fun U : ActualRootPreparation G ell q=>U.frame.words) literal) (atlasUsingShared X S)

theorem ready_atlas_is_literal : (readyAtlas X S literal).result=X.atlas.result := by
  subst S
  exact (shared_atlas_is_literal X).1.symm

noncomputable def preparedSeed (pad : ℕ) : PageJob f ell key prec tw bw (pageKeyWidth m+pad) :=
  let H := headerUsingShared X S
  let B := readyAtlas X S literal
  have tag : loadAt prec (externalAddrWidth tc tj 0) H.result.bytes=
      ⟨some X.frame.birth,headerReadFee prec (externalAddrWidth tc tj 0)⟩ := by
    have same : H.result=X.header.result := by
      subst S
      exact (shared_header_is_literal X).1.symm
    rw [same]
    exact (stable_exterior_header X).2.1
  have pageOK : B.result=some (rootTable X.chosenFields) := by
    change (readyAtlas X S literal).result=_
    rw [ready_atlas_is_literal X S literal]
    exact (Classical.choose_spec (stable_exterior_atlas X)).1
  rootJob X.frame H (externalAddrWidth tc tj 0) X.context tag pad B
    (rootTable X.chosenFields) pageOK

theorem same_seed_bytes (pad : ℕ) :
    let fresh := preparedSeed X S literal pad
    let old := X.seed pad
    fresh.entry.result=old.entry.result ∧ fresh.identifier=old.identifier ∧ fresh.immutable=old.immutable := by
  have h : (headerUsingShared X S).result=X.header.result := by
    subst S
    exact (shared_header_is_literal X).1.symm
  let fresh := preparedSeed X S literal pad
  let old := X.seed pad
  refine ⟨h,congrArg DirRow.id h,?_⟩
  change publishedRow (headerUsingShared X S).result X.birth X.context
       (⟨X.frame,(rootTable X.chosenFields).map (mappedRow pad)⟩ : PagedEnvelope f ell prec (pageKeyWidth m+pad))=
    publishedRow X.header.result X.birth X.context
       (⟨X.frame,(rootTable X.chosenFields).map (mappedRow pad)⟩ : PagedEnvelope f ell prec (pageKeyWidth m+pad))
  rw [h]

theorem prepared_seed_same_live (pad : ℕ) (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :
    IsLive (preparedSeed X S literal pad) B ↔ IsLive (X.seed pad) B := by
  obtain ⟨h,id,payload⟩ := same_seed_bytes X S literal pad
  unfold IsLive
  rw [h,id,payload]

theorem prepared_seed_exact_install (pad : ℕ) (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (sync : B.synced) (fresh : ∀ row∈B.headers,row.id≠(X.seed pad).identifier) :
    let j := preparedSeed X S literal pad
    let old := X.seed pad
    (j.install B).result=(old.install B).result ∧
      (j.install B).steps=publishFee B j.entry j.offset j.built := by
  let j := preparedSeed X S literal pad
  let old := X.seed pad
  have eq : j.entry.result=old.entry.result ∧ j.identifier=old.identifier ∧ j.immutable=old.immutable :=
    same_seed_bytes X S literal pad
  have ready (K : PageJob f ell key prec tw bw (pageKeyWidth m+pad))
      (who : K.identifier=old.identifier) : JobsReady B [K] := by
    refine ⟨sync,by simp,?_⟩
    intro l hl row hr
    obtain rfl := List.mem_singleton.mp hl
    rw [who]
    exact fresh row hr
  have a := (next_job_exact B j [] (ready j eq.2.1)).1
  have b := (next_job_exact B old [] (ready old rfl)).1
  have eqState : afterOne B j=afterOne B old := by
    unfold afterOne
    rw [eq.1,eq.2.2]
  change (j.install B).result=(old.install B).result ∧ (j.install B).steps=_
  rw [a,b,eqState]
  exact ⟨rfl,rfl⟩

end Root

#print axioms ready_atlas_is_literal
#print axioms same_seed_bytes
#print axioms prepared_seed_same_live
#print axioms prepared_seed_exact_install
end J6R35GatewayPreparation
