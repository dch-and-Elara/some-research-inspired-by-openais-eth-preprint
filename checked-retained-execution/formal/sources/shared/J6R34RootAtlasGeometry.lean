import J6R34RootAtlasStable

/-! Source semantics of each actually installed root page. Equality of
whole banks comes from the same actual compiler, and equality of the
selected data comes from the true injective Page lookup. -/
namespace J6R34RootAtlas
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R30ProducedGateRegistry
open J6R32RootGeneratedRegistryInputs J6R33PageIndexedBirth
open J6R15ModeCost J6R27OriginalGate J6R17ModeTape J6R18ChildWrite J6R21Ancestor
open J6R14ZeroMode J6R27PrescribedProbe J6R26StablePreparedRoot J6R16ModeCost J6R20Ancestor
set_option maxHeartbeats 8500000

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q r c d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q r c d edgew tc tj key prec tw bw)

theorem stable_seed_true_page_law (k : Page (a m) (K m) (Fin 64)) :
    let i := oddAxis m
    let p := J6SourcePrecision.printed m base
    let P := rootChart T
    let F := X.chosenFields k
    let N := (writeResidents m X.hq i X.copies X.pre X.source.raw).result.roster.modes.length
    let rows := sourceRows P i X.group k (actualWires m)
    let cols := sourceCols P i X.group k (actualWires m)
    F.rows=rows.map (fun row=>slotWord P row.val) ∧
      F.cols=cols.map (fun col=>slotWord P col.val) ∧ rows.Nodup ∧ cols.Nodup ∧
      (∀ row,row∈rows) ∧ (∀ col,col∈cols) ∧
      ∃ ξ : Fin N≃PacketMode i (K m) (2^(i.val+1)) p,∃ ms : Fin N→ModeInput (a m) p i q,
        F.modes=List.ofFn ms ∧
        ModeMeaning P i X.group k (ξ.trans (packet_mode_equiv P.mask i p).symm) 0 ms ∧
        ∀ u,(ms u).code=encodeBits X.code u.succ.val := by
  let B := buildRootBitBank G ell
  obtain ⟨expected,yes,_,hits,laws,_⟩ := actual_prescribed_root_atlas X.source X.field.result X.hf X.positive
    B.result X.sample X.hq (oddAxis m) X.qFits X.copies X.pre X.copiesOK X.precOK X.group X.code
    X.codePos X.codeValid X.copyFits
  have actual := Classical.choose_spec (stable_exterior_atlas X)
  have comp : X.atlas.result=some (rootTable expected) := yes
  have eq : rootTable X.chosenFields=rootTable expected := Option.some.inj (actual.1.symm.trans comp)
  have chosen : (locate (residentPageKey m k) (rootTable X.chosenFields)).result=some (X.chosenFields k) :=
    actual.2.1 k
  rw [eq,hits k] at chosen
  have e : X.chosenFields k=expected k := (Option.some.inj chosen).symm
  obtain ⟨ξ,ms,_,rows,cols,modes,sem,codes⟩ := laws k
  let W := writeResidents m X.hq (oddAxis m) X.copies X.pre X.source.raw
  have seat := (actual_root_resident_tables X.source X.hq (oddAxis m) X.qFits X.copies X.pre
    X.copiesOK X.precOK X.field.result.hp).2.1
  obtain ⟨hW,hA⟩ := ordered_wires_exact (J6R28GeneratedRootFrame.constantRootWord m)
    (printed_room m) (printed_half_correct m)
  obtain ⟨_,_,rN,cN,rAll,cAll⟩ := physical_slots_emitted (rootChart T) (oddAxis m) (residentPageKey m)
    (resident_page_key_injective m) X.group k (actualWires m) hW hA W.result.seats seat
  dsimp only
  rw [e]
  exact ⟨rows,cols,rN,cN,rAll,cAll,ξ,ms,modes,sem,codes⟩

#print axioms stable_seed_true_page_law
end J6R34RootAtlas
