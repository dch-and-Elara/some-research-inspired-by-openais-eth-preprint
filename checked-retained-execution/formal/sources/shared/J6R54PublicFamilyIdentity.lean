import J6R54PublicFamilySite

/-! With a fixed reserved owner marker, different real public triples
cannot issue the same raw key. No statement of freshness against an
arbitrary external or native registry follows from this result. -/
namespace J6R54PublicFamily
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6Mesh J6OrientedHost J6R15ModeCost
open J6R24LegalLayout J6R26StablePreparedRoot J6R28GeneratedRootFrame
open J6R14ZeroMode J6R34RootAtlas J6R33StatefulArithmeticPage J6R32StatefulArithmetic J6R31RootResidentTables J6R30ProducedGateRegistry
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)

theorem actual_public_owner_injective
    {i i' : J6Recovery.Addr m} {j j' : Fin (literalDegree m native+1)} {g g' : Fin 64}
    (same : (siteFromHead W g C (prepareHead W i j).result).result.issue.result =
      (siteFromHead W g' C (prepareHead W i' j').result).result.issue.result) :
    i=i' ∧ j=j' ∧ g=g' := by
  let H := (prepareHead W i j).result
  let H' := (prepareHead W i' j').result
  change (issueExterior C.mark (realAddress H.data g).result).result =
    (issueExterior C.mark (realAddress H'.data g').result).result at same
  obtain ⟨t,s,b⟩ := issued_exterior_equal_address same
  have tval := congrArg Word.val t
  have sval := congrArg Word.val s
  have bval := congrArg Word.val b
  have H₀ := real_address_exact H.data g
  have H₁ := real_address_exact H'.data g'
  rw [H₀.1,H₁.1,H.centreOK,H'.centreOK] at tval
  rw [H₀.2.1,H₁.2.1,H.sampleOK,H'.sampleOK] at sval
  rw [H₀.2.2.1,H₁.2.2.1] at bval
  refine ⟨Fin.ext ?_,Fin.ext sval,Fin.ext bval⟩
  unfold index at tval
  omega

theorem actual_public_owner_marker
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
    ((siteFromHead W g C (prepareHead W i j).result).result.issue.result.bits.take kp)=C.mark.bits := by
  let H := (prepareHead W i j).result
  let A := (realAddress H.data g).result
  have E := congrArg Word.bits (issued_exterior_exact C.mark A).1
  change (issueExterior C.mark A).result.bits=C.mark.bits++(A.centre.bits++(A.sample.bits++A.group.bits)) at E
  change ((issueExterior C.mark A).result.bits.take kp)=C.mark.bits
  rw [E]
  let tail := A.centre.bits++(A.sample.bits++A.group.bits)
  have change_take := congrArg (fun n : ℕ => List.take n (C.mark.bits++tail)) C.mark.size.symm
  exact change_take.trans (by simp)

theorem actual_public_live_from_common_bank
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (pad : ℕ)
    (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (sync : B.synced)
    (guard : ∀ r∈B.headers,r.id.bits.take kp≠C.mark.bits) :
    let X := (siteFromHead W g C (prepareHead W i j).result).result
    let Y := X.seed pad
    (Y.install B).result.2=true ∧ IsLive Y (Y.install B).result.1 := by
  let X := (siteFromHead W g C (prepareHead W i j).result).result
  let Y := X.seed pad
  have id : Y.identifier=X.issue.result := (stable_exterior_header X).1
  have fresh : ∀ r∈B.headers,r.id≠Y.identifier := by
    intro r hr e
    apply guard r hr
    rw [e,id]
    exact actual_public_owner_marker W C i j g
  have H : JobsReady B [Y] := by
    refine ⟨sync,by simp,?_⟩
    intro d hd r hr
    obtain rfl := List.mem_singleton.mp hd
    exact fresh r hr
  change (Y.install B).result.2=true ∧ IsLive Y (Y.install B).result.1
  rw [(next_job_exact B Y [] H).1]
  exact ⟨rfl,new_is_live Y B⟩

#print axioms actual_public_owner_injective
#print axioms actual_public_owner_marker
#print axioms actual_public_live_from_common_bank
end
end J6R54PublicFamily

