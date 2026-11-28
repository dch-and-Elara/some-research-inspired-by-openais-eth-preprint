import J6R49NonModeStackPayload
import J6R22ActiveCenter

/-! Observable decomposition of the original paid right fold. Under
head-before-tail evaluation the list represents one completed result
per suspended frame; this is not a replacement runner or a heap model. -/
namespace J6R49NonModeStack
open A1R10 AOracleMachineTime J6R21Leaf J6R22Active
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000

variable {p ell k n : ℕ} {fw : List (A1R10.Word p)}
variable (hp : 0<p) (he : 0<fw.length)

abbrev J (fw : List (A1R10.Word p)) (ell k : ℕ) := Meter (JetTape fw ell k)

def joinJet (x y : J fw ell k) : J fw ell k :=
  let z := jetAdd hp he x.result y.result
  ⟨z.result,x.steps+y.steps+z.steps+2⟩

def unwind (saved : List (J fw ell k)) (tail : J fw ell k) : J fw ell k :=
  saved.foldr (joinJet hp he) tail

/-- Exact recovery of both result and the original meter from the
finished head results and the still-pending suffix. -/
theorem paid_jet_sum_suspend {A : Type*} (op : A→J fw ell k) (left right : List A) :
    paidJetSum hp he op (left++right)=
      unwind hp he (left.map op) (paidJetSum hp he op right) := by
  induction left with
  | nil => rfl
  | cons a xs ih => simp only [List.cons_append,List.map_cons,paidJetSum,unwind,List.foldr_cons,
      joinJet,ih]

variable (hv : 0<ell) (hk : 0<k)

def finishTerm (b : J fw ell k) (sample : Meter (UVBlock fw ell)) : J fw ell k :=
  let out := jetMult hp he (jetConst hp he hk sample.result) b.result
  ⟨out.result,b.steps+sample.steps+out.steps+tapeFee fw.length ell p k+4⟩

theorem interp_term_uses_basis_and_one_word
    (node sample : Fin n→Meter (UVBlock fw ell)) (i : Fin n) :
    interpTerm hp he hv hk node sample i=
      finishTerm hp he hk (basisM hp he hv hk node i) (sample i) := rfl

theorem probe_order_split (i : Fin n) :
    probeOrder n=(probeOrder n).take i.val ++ (i::(probeOrder n).drop (i.val+1)) := by
  have hi : i.val < (probeOrder n).length := by simpa only [probeOrder,List.length_ofFn] using i.isLt
  have eq : (probeOrder n)[i.val]=i := by simp [probeOrder]
  calc
    probeOrder n=(probeOrder n).take i.val ++ (probeOrder n).drop i.val :=
      (List.take_append_drop i.val (probeOrder n)).symm
    _=_ := by rw [List.drop_eq_getElem_cons hi,eq]

def completedTerms (node sample : Fin n→Meter (UVBlock fw ell)) (i : Fin n) :
    List (J fw ell k) :=
  ((probeOrder n).take i.val).map (interpTerm hp he hv hk node sample)

theorem completed_terms_length (node sample : Fin n→Meter (UVBlock fw ell)) (i : Fin n) :
    (completedTerms hp he hv hk node sample i).length=i.val := by
  unfold completedTerms
  rw [List.length_map,List.length_take]
  simp only [probeOrder,List.length_ofFn,min_eq_left i.isLt.le]

theorem completed_terms_use_only_earlier_samples
    (node sample other : Fin n→Meter (UVBlock fw ell)) (i : Fin n)
    (same : ∀ j : Fin n,j.val < i.val → sample j=other j) :
    completedTerms hp he hv hk node sample i=completedTerms hp he hv hk node other i := by
  unfold completedTerms
  apply List.map_congr_left
  intro j hj
  obtain ⟨u,hu,atU⟩ := List.mem_take_iff_getElem.mp hj
  have e : u=j.val := by
    have h := congrArg Fin.val atU
    simpa only [probeOrder,List.getElem_ofFn] using h
  have hJ : j.val < i.val := e ▸ (lt_of_lt_of_le hu (min_le_left _ _))
  simp only [interp_term_uses_basis_and_one_word,same j hJ]

/-- Pause during the real probe's native child callback, after building
this probe's basis and before acquiring its reply. Outcome and accounting
are exactly the old `interpPrefix` when unwound after that reply. -/
theorem interp_prefix_pause_exact
    (node sample : Fin n→Meter (UVBlock fw ell)) (i : Fin n) :
    let saved := completedTerms hp he hv hk node sample i
    let later := paidJetSum hp he (interpTerm hp he hv hk node sample) ((probeOrder n).drop (i.val+1))
    let current := finishTerm hp he hk (basisM hp he hv hk node i) (sample i)
    let recovered := unwind hp he saved (joinJet hp he current later)
    interpPrefix hp he hv hk node sample=
      ⟨recovered.result,recovered.steps+4*(n+1)^2+4⟩ := by
  let f := interpTerm hp he hv hk node sample
  have eq :
      paidJetSum hp he f (probeOrder n)=
        unwind hp he (completedTerms hp he hv hk node sample i)
          (joinJet hp he (finishTerm hp he hk (basisM hp he hv hk node i) (sample i))
            (paidJetSum hp he f ((probeOrder n).drop (i.val+1)))) :=
    calc
      _ = paidJetSum hp he f ((probeOrder n).take i.val ++ (i::(probeOrder n).drop (i.val+1))) :=
        congrArg (paidJetSum hp he f) (probe_order_split i)
      _ = _ := by
        rw [paid_jet_sum_suspend]
        rfl
  dsimp only
  unfold interpPrefix
  rw [eq]

/-- Payload of the paused prefix, its current basis, and a normalizer
already carried into `fullCenterM`. No raw reply, arithmetic scratch,
pointer/fee metadata, or child frames are included in this payload. -/
def pausedJetFields (node sample : Fin n→Meter (UVBlock fw ell)) (i : Fin n)
    (normal : J fw ell k) : List Bool :=
  keptPayload (completedTerms hp he hv hk node sample i) ++
    jetPayload (basisM hp he hv hk node i).result ++ jetPayload normal.result

theorem paused_jet_fields_exact (node sample : Fin n→Meter (UVBlock fw ell)) (i : Fin n)
    (normal : J fw ell k) :
    (pausedJetFields hp he hv hk node sample i normal).length=
      (i.val+2)*(k*scalarWidth fw.length ell p) := by
  unfold pausedJetFields
  simp only [List.length_append,kept_payload_length,completed_terms_length,jet_payload_length]
  simp only [Nat.add_mul,Nat.two_mul,Nat.add_assoc]

theorem paused_jet_fields_bound (node sample : Fin n→Meter (UVBlock fw ell)) (i : Fin n)
    (normal : J fw ell k) :
    (pausedJetFields hp he hv hk node sample i normal).length≤
      (n+1)*(k*scalarWidth fw.length ell p) := by
  rw [paused_jet_fields_exact]
  exact Nat.mul_le_mul_right _ (by omega)

#print axioms paid_jet_sum_suspend
#print axioms interp_term_uses_basis_and_one_word
#print axioms probe_order_split
#print axioms completed_terms_length
#print axioms completed_terms_use_only_earlier_samples
#print axioms interp_prefix_pause_exact
#print axioms paused_jet_fields_exact
#print axioms paused_jet_fields_bound
end J6R49NonModeStack
