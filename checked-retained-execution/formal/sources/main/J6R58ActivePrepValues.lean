import J6R58ActivePrepCentre

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13000000
set_option maxRecDepth 1700
set_option linter.unusedSectionVars false
set_option Elab.async false

/-! Replacing the paid mask reader does not replace the arithmetic
or its typed probe addresses. Every exact resulting coefficient word
is unchanged for the same child responses. No equality of fees is
used in the value argument. -/
namespace J6R58ActivePrep
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R49DFS

theorem product_reads_same_words {A : Type*} {p ell k : ℕ} {fw : List (A1R10.Word p)}
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (hk : 0<k)
    (F G : A→Meter (JetTape fw ell k)) (eq : ∀ i,(F i).result=(G i).result)
    (xs : List A) :
    (paidJetProd hp he hv hk F xs).result=(paidJetProd hp he hv hk G xs).result := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [paidJetProd,eq x,ih]

theorem centre_same_node_words {p ell k n : ℕ} {fw : List (A1R10.Word p)}
    (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (hk : 0<k)
    (u v samples : Fin n→Meter (UVBlock fw ell)) (normal : Meter (JetTape fw ell k))
    (eq : ∀ i,(u i).result=(v i).result) :
    (fullCenterM hp he hv hk u samples normal).result=
      (fullCenterM hp he hv hk v samples normal).result := by
  have basis (i : Fin n) :
      (basisM hp he hv hk u i).result=(basisM hp he hv hk v i).result := by
    change (paidJetProd hp he hv hk (fun j=>factorM hp he hv hk (u i).result (u j))
      (offDiagonal i)).result=
      (paidJetProd hp he hv hk (fun j=>factorM hp he hv hk (v i).result (v j))
        (offDiagonal i)).result
    apply product_reads_same_words
    intro j
    simp only [factorM,eq i,eq j]
  have term (i : Fin n) :
      (interpTerm hp he hv hk u samples i).result=(interpTerm hp he hv hk v samples i).result := by
    simp only [interpTerm,basis i]
  have H := paid_jets_same_values hp he (interpTerm hp he hv hk u samples)
    (interpTerm hp he hv hk v samples) (probeOrder n) (fun j _=>term j)
  simp only [fullCenterM,interpPrefix,H]

noncomputable section
variable {f : ℤ[X]} {ell s q n : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) c}
variable {bank : Bank f} {fit : n≤2^f.natDegree}
local notation "P" => (printedParams (f:=f) (ell:=ell) s)

theorem same_centre_jet_words (hf : f.Monic) (B : MaskTable f.natDegree n fit)
    (subsetCount : physicalProbeCount f ell s c≤n) (J : CentreMachine sel d t bank q) (hq : 0<q) (hv : 0<ell)
    (read : CentreChild (sel:=sel) (d:=d) (t:=t) bank) :
    ((centreWithChart hf B subsetCount J).centreJet hq hv read).result=(J.centreJet hq hv read).result := by
  unfold CentreMachine.centreJet directCentreJet
  apply centre_same_node_words
  intro z
  change (encodeProbe J.low.hp hv (chartMask hf B subsetCount J z).result).result=
    (encodeProbe J.low.hp hv (J.masks z).result).result
  rw [chart_mask_word]

theorem same_centre_value (hf : f.Monic) (B : MaskTable f.natDegree n fit)
    (subsetCount : physicalProbeCount f ell s c≤n) (J : CentreMachine sel d t bank q) (hq : 0<q) (hv : 0<ell)
    {pHigh : ℕ} (H : Frame f pHigh) (excess : ℕ)
    (read : CentreChild (sel:=sel) (d:=d) (t:=t) bank) :
    ((centreWithChart hf B subsetCount J).runCentre hq hv hf H excess read).result=
      (J.runCentre hq hv hf H excess read).result := by
  change (sumM H.hp (J.centreTerm hv hf H excess
    ((centreWithChart hf B subsetCount J).centreJet hq hv read).result) (List.range J.window)).result=
    (sumM H.hp (J.centreTerm hv hf H excess (J.centreJet hq hv read).result)
      (List.range J.window)).result
  rw [same_centre_jet_words]

theorem same_active_value (hf : f.Monic) (B : MaskTable f.natDegree n fit)
    (subsetCount : physicalProbeCount f ell s c≤n) (A : ActiveMachine sel d bank q) (hq : 0<q) (hp : 0<c.prec)
    (hv : 0<ell) (read : ActiveChild (sel:=sel) (d:=d) bank) :
    ((activeWithChart hf B subsetCount A).eval hq hp hv hf read).result=
      (A.eval hq hp hv hf read).result := by
  let V := activeWithChart hf B subsetCount A
  have eqHigh : (V.highRun hq hp hv hf read).result=(A.highRun hq hp hv hf read).result := by
    apply sum_raw_congr
    intro t _
    exact same_centre_value hf B subsetCount (A.tape t) hq hv (A.high hp) A.extraPrecision (read t)
  have eqFin : (V.finish hq hp hv hf read).result=(A.finish hq hp hv hf read).result := by
    simp only [ActiveMachine.finish,eqHigh]
  change (V.eval hq hp hv hf read).result=(A.eval hq hp hv hf read).result
  simp only [ActiveMachine.eval,checkedWord,eqFin]
  cases (A.finish hq hp hv hf read).result <;> rfl

#print axioms product_reads_same_words
#print axioms centre_same_node_words
#print axioms same_centre_jet_words
#print axioms same_centre_value
#print axioms same_active_value
end
end J6R58ActivePrep

