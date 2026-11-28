import J6R36SharedGatewayTop

/-! A direct equality of the two original typed API functions, not
only their legal projections. Therefore the new metered result is
the same final word as the old gateway on the same witnesses. -/
namespace J6R36SharedGateway
open scoped Polynomial Classical
open Polynomial Std.Sat AOracleMachineTime A1R10
open J6Mesh J6OrientedHost J7R10Plant J6R24LegalLayout J6R24MeteredRecursion J6R25StableCensus
open J6R35GatewayPreparation J6R34OfficialGateway J6R33OriginalJ6
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R14ZeroMode J6R28GeneratedRootFrame
set_option maxHeartbeats 10000000
set_option maxRecDepth 2300
set_option linter.unusedSectionVars false

section Source
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd edgew tc tj key prec tw bw pad : ℕ}
variable {C : CommonInputs (T:=T) (f:=f) (base:=base) ell q rr cc dd}
variable (S : ActualRootPreparation G ell q) (hold : S=(CommonInputs.make (G:=G) C).result)
variable (routes : SharedRequests G C pad edgew tc tj key prec tw bw)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem same_original_oracle :
    cachedOracle S hold routes=freshlyBuiltOracle routes := by
  have entry : (cachedOracle S hold routes).reply=(freshlyBuiltOracle routes).reply := by
    funext i j raw
    by_cases h : raw=writtenProbe (ell:=ell) G j
    · exact (cached_all64_reply_equals_fresh S hold routes i j raw
        (h.trans (S.probes.consistent j).symm)).2.1
    · simp only [cachedOracle,freshlyBuiltOracle,sourceAtlasOracle,completedOracle,if_neg h]
  cases eq : cachedOracle S hold routes with
  | mk L hL =>
    cases eq' : freshlyBuiltOracle routes with
    | mk R hR =>
      rw [eq,eq'] at entry
      change L=R at entry
      subst R
      rfl

end Source

section Final
variable {V : Type} [DecidableEq V] [Fintype V] [Nonempty V]
variable {f : ℤ[X]} {F : CNF V} {base ell q rr cc dd edgew tc tj key prec tw bw : ℕ}
local notation "ms" => J7R10Readout.mCNF
local notation "qs" => J7R10Readout.qCNF
variable (G : RootShape f (ms F) (printedHalf (ms F)) base (literalNativeSize F)
  (printedRankWidth (ms F)) (physicalPlant (J7R10Readout.H F)) (constantRootWord (ms F)))
variable (C : CommonInputs (T:=physicalPlant (J7R10Readout.H F)) (f:=f) (base:=base) ell q rr cc dd)
variable (pad : ℕ)
variable (routes : SharedRequests G C pad edgew tc tj key prec tw bw)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem shared_same_final_raw_word :
    let m := ms F
    let w := constantRootWord m
    let W := printed_readout_fits m (qs F) base w
    let old := oracleCount F base (printedHalf m) (literalNativeSize F) (printedRankWidth m)
      (printedFactorWidth m (qs F)) (printedAnswerWidth m base) w G C.field.result C.hf C.positive
      W.1 W.2.1 (freshlyBuiltOracle routes)
    (runWithOneSharedRoot G C pad routes).result=old.result := by
  let cache := (CommonInputs.make (G:=G) C).result
  obtain ⟨one,_⟩ := operation_costs_reach_final_word G C pad routes cache rfl
  have fronts := (original_frontend_and_no_duplicate_bank G C pad routes cache rfl).1
  simpa only [ordinaryFrontend,same_original_oracle cache rfl routes] using one.trans fronts.symm

end Final

#print axioms same_original_oracle
#print axioms shared_same_final_raw_word
end J6R36SharedGateway