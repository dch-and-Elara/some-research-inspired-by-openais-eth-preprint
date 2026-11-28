import J6R33OriginalJ6Oracle

namespace J6R33OriginalJ6
open scoped Classical Polynomial BigOperators
open Polynomial A1R10 A1R11 AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost J6R9Recursive J6R11Repack J6R12Repack
open J6R14ZeroMode J6R22Active J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe
open J6ActiveRun J6ActiveSchedule
set_option maxHeartbeats 7500000
set_option maxRecDepth 2200
set_option linter.unusedSectionVars false

def rootSiteFee (e m d ell p : ℕ) (hp : 0<p) : ℕ :=
  let n := d+1
  n*(n*(e+2)+slotCommFee e m d ell p)+
  n^2*(n*(e+2)+e*(p+6)+uvWidth e ell p+4)+
  interpExtra e ell p 1 n hp+jetCoeffFee e ell p 1+3

theorem same_site_fee (p₁ p e₁ e m d ell : ℕ) (hp₁ : 0<p₁) (hp : 0<p)
    (H : p₁=p) (E : e₁=e) :
    rootSiteFee e₁ m d ell p₁ hp₁=rootSiteFee e m d ell p hp := by
  subst p₁
  subst e₁
  rfl

section Source
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m l q base native width ell : ℕ}
variable {T : Plant V m q} {w : Fin (a m)→Fin 64}
variable (G : RootShape f m l base native width T w)
variable {F : Frame f (J6SourcePrecision.printed m base)} {hf : f.Monic}
local notation "d₀" => literalDegree m native

theorem oracle_site_paid (A : SuppliedProbeBits (rootPreset G ell) f.natDegree)
    (readBound : ∀ j,(A.read j).steps≤(d₀+1)*(f.natDegree+2))
    (O : CompletedOracle G ell F hf) (hv : 0<ell)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] (i : J6Recovery.Addr m) :
    (oracleSite G A O hv i).steps ≤ rootSiteFee f.natDegree m d₀ ell _ F.hp := by
  let E := SiteFrame G ell F i
  let pr := registerPrecision (rootParams f ell m native)
    (physicalRootCall f ell base m l q T w) (G.centre ell i)
  let read := siteReader (F:=F) (hf:=hf) G A i
  let node := readPrescribed E.hp hv read
  let sample := callSlot G A O i
  let e := E.words.length
  let n := d₀+1
  have a : e=f.natDegree := E.natDegree hf
  have hp : pr=J6SourcePrecision.printed m base := G.precision ell i
  have samples (j : Fin n) : (sample j).steps≤n*(e+2)+slotCommFee e m d₀ ell pr := by
    rw [a,hp]
    exact (actual_completed_slot G A O i j).2.trans (Nat.add_le_add_right (readBound j) _)
  have nodes (j : Fin n) : (node j).steps≤n*(e+2)+e*(pr+6)+uvWidth e ell pr+4 := by
    have rtc := (read_prescribed_exact E.hp hv (rootPreset G ell) E.exactMod read
      (fun j=>A.consistent j) j).2
    change (node j).steps=(A.read j).steps+(e*(pr+6)+uvWidth e ell pr+2)+2 at rtc
    rw [rtc,a]
    have R : (A.read j).steps≤n*(f.natDegree+2) := readBound j
    omega
  have s := uniform_word_bill sample (n*(e+2)+slotCommFee e m d₀ ell pr) samples (probeOrder n)
  rw [show (probeOrder n).length=n from List.length_ofFn] at s
  have b : interpBill node sample≤bill sample (probeOrder n)+n^2*
      (n*(e+2)+e*(pr+6)+uvWidth e ell pr+4) :=
    interp_charged_repeated_reads node sample _ nodes
  have cost := (oracle_site_exact G A O hv i).2
  change (oracleSite G A O hv i).steps ≤
      interpBill node sample+interpExtra e ell pr 1 n E.hp+jetCoeffFee e ell pr 1+3 at cost
  have c : (oracleSite G A O hv i).steps ≤ rootSiteFee e m d₀ ell pr E.hp := by
    unfold rootSiteFee
    change _≤n*(n*(e+2)+slotCommFee e m d₀ ell pr)+
      n^2*(n*(e+2)+e*(pr+6)+uvWidth e ell pr+4)+
      interpExtra e ell pr 1 n E.hp+jetCoeffFee e ell pr 1+3
    omega
  exact c.trans (le_of_eq (same_site_fee pr _ e _ m d₀ ell E.hp F.hp hp a))
end Source

def requestTrace (m d : ℕ) : List (Fin (m+1)×Fin (d+1)) :=
  (probeOrder (m+1)).flatMap (fun i=>(probeOrder (d+1)).map (Prod.mk i))

theorem paired_schedule {α β : Type} (A : List α) (B : List β) :
    (A.flatMap (fun i=>B.map (Prod.mk i))).length=A.length*B.length := by
  induction A with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_mul,Nat.add_comm]

theorem request_trace_exact (m native : ℕ) (good : native≤m) :
    (requestTrace m (literalDegree m native)).length=fallbackAddresses m ∧
    (requestTrace m (literalDegree m native)).length≤
      (m+1)*(2*(2*(m+2))^(524288+8)+1) := by
  have q : (requestTrace m (literalDegree m native)).length=fallbackAddresses m := by
    unfold requestTrace fallbackAddresses
    rw [paired_schedule,literal_degree_eq m native good]
    simp only [probeOrder,List.length_ofFn]
  exact ⟨q,q.le.trans (fallbackAddresses_polynomial m)⟩

#print axioms same_site_fee
#print axioms oracle_site_paid
#print axioms paired_schedule
#print axioms request_trace_exact
end J6R33OriginalJ6
