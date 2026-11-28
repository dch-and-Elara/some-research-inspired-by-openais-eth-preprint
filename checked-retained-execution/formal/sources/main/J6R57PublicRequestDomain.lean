import J6R57PublicRequestBind

/-! No implicit successful branch: addresses and probe words must
both match their legal printed entry. This is an exact iff for the
generated finite request language, not just existence at valid rows. -/
namespace J6R57PublicRequest
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4000
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (C : Compiled G ell q rr cc dd prec kp bw) (D : PreparedRequests W C)

theorem complete_printed_request_language (addr : OccurrenceAddress tc tj) (raw : List Bool) :
    (readPublicRequest C D addr raw).result.isSome ↔
      ∃ x : Coordinate m native,
        addr.centre.val=index m x.1.1 ∧ addr.sample.val=x.1.2.val ∧ addr.group.val=x.2.val ∧
        raw=List.ofFn ((rootPreset G ell).word x.1.2) := by
  constructor
  · intro ok
    have formula :
        (readPublicRequest C D addr raw).result=
          match (rawRequest C.mark addr D.rows).result with
          | none => none
          | some r => (gateSample C D r raw).result := by
      unfold readPublicRequest
      dsimp only
      cases condition : (rawRequest C.mark addr D.rows).result <;> rfl
    rw [formula] at ok
    cases classified : (rawRequest C.mark addr D.rows).result with
    | none =>
      rw [classified] at ok
      cases ok
    | some r =>
      have receiving : (rawRequest C.mark addr D.rows).result.isSome := by rw [classified]; rfl
      have legal : LegalAddress m native addr := by
        apply (native_raw_request_exact_domain W C.mark addr).mp
        rwa [←D.ordered]
      obtain ⟨x,t,j,g⟩ := legal
      have expected : (rawRequest C.mark addr D.rows).result=some (emitAt W C.mark x).result := by
        rw [D.ordered]
        exact (native_raw_request_hit W C.mark addr x t j g).1
      have same : r=(emitAt W C.mark x).result := Option.some.inj (classified.symm.trans expected)
      rw [classified] at ok
      have exactBytes := (prescribed_sample_accepted C D r raw).mp ok
      rw [same] at exactBytes
      exact ⟨x,t,j,g,exactBytes⟩
  · rintro ⟨x,t,j,g,bytes⟩
    rw [(true_prescribed_address_is_found C D addr x t j g raw bytes).1]
    rfl

#print axioms complete_printed_request_language
end
end J6R57PublicRequest
