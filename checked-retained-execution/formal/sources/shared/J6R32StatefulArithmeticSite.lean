import J6R32StatefulArithmeticFolds

/-! Local ordered reconstruction: each basis is prepared at its literal
probe index, then that sample's mode and group calls are run with a
single threaded directory, then the existing bit operations consume
their result. Normalizer, jet division, Hermite terms and strip remain
the previously audited meter kernels. -/
namespace J6R32StatefulArithmetic
open AOracleMachineTime A1R10 A1R12 J6R22Active

variable {S : Type*} {p ell n k : ℕ} {fw : List (Word p)}
variable (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (hk : 0<k)

def padWord {A : Type*} (cost : ℕ) (x : A) : Meter A := ⟨x,cost⟩

theorem merge_pad {A : Type*} (x : Meter A) (cost : ℕ) :
    merge x (padWord cost)=padCost x cost := rfl

def termS (node : Fin n→Meter (UVBlock fw ell)) (sample : Fin n→SM S (UVBlock fw ell))
    (i : Fin n) : SM S (JetTape fw ell k) :=
  combine (stationary (basisM hp he hv hk node i)) (sample i)
    (fun b y=>padCost (jetMult hp he (jetConst hp he hk y) b) (tapeFee fw.length ell p k+4))

theorem term_sound {I : S→Prop} (node : Fin n→Meter (UVBlock fw ell))
    (sample : Fin n→SM S (UVBlock fw ell)) (ref : Fin n→Meter (UVBlock fw ell))
    (i : Fin n) (sub : Sound I (sample i) (ref i)) :
    Sound I (termS hp he hv hk node sample i) (interpTerm hp he hv hk node ref i) := by
  have H := (stationary_sound I (basisM hp he hv hk node i)).combine sub
    (fun b y=>padCost (jetMult hp he (jetConst hp he hk y) b) (tapeFee fw.length ell p k+4))
  simpa only [termS,merge2,padCost,interpTerm,Nat.add_assoc] using H

def prefixS (node : Fin n→Meter (UVBlock fw ell)) (sample : Fin n→SM S (UVBlock fw ell)) :
    SM S (JetTape fw ell k) :=
  finish (sumJets hp he (termS hp he hv hk node sample) (probeOrder n)) (padWord (4*(n+1)^2+4))

theorem prefix_sound {I : S→Prop} (node : Fin n→Meter (UVBlock fw ell))
    (sample : Fin n→SM S (UVBlock fw ell)) (ref : Fin n→Meter (UVBlock fw ell))
    (sub : ∀ i,Sound I (sample i) (ref i)) :
    Sound I (prefixS hp he hv hk node sample) (interpPrefix hp he hv hk node ref) := by
  have H := sumJets_sound hp he (termS hp he hv hk node sample)
    (interpTerm hp he hv hk node ref) (probeOrder n) (fun z _=>term_sound hp he hv hk node sample ref z (sub z))
  have Q := H.finish (padWord (4*(n+1)^2+4))
  simpa only [prefixS,merge_pad,padCost,interpPrefix,Nat.add_assoc] using Q

def fullS (node : Fin n→Meter (UVBlock fw ell)) (sample : Fin n→SM S (UVBlock fw ell))
    (normal : Meter (JetTape fw ell k)) : SM S (JetTape fw ell k) :=
  combine (stationary normal) (prefixS hp he hv hk node sample)
    (fun E j=>padCost (divideJet hp he hv hk E j) 4)

theorem full_sound {I : S→Prop} (node : Fin n→Meter (UVBlock fw ell))
    (sample : Fin n→SM S (UVBlock fw ell)) (ref : Fin n→Meter (UVBlock fw ell))
    (normal : Meter (JetTape fw ell k)) (sub : ∀ i,Sound I (sample i) (ref i)) :
    Sound I (fullS hp he hv hk node sample normal) (fullCenterM hp he hv hk node ref normal) := by
  have h := (stationary_sound I normal).combine (prefix_sound hp he hv hk node sample ref sub)
    (fun E j=>padCost (divideJet hp he hv hk E j) 4)
  simpa only [fullS,merge2,padCost,fullCenterM,Nat.add_assoc] using h

section Physical
variable {Mode : Type*}
def siteS (J : SiteTape p ell k n Mode) (a : ℕ) (t : ℤ)
    (child : Fin n→Mode→Fin 64→SM S (UVBlock J.fw ell)) :
    SM S (JetTape J.fw ell k) :=
  fullS J.hp J.nonempty J.he J.hk J.nodeM
    (fun z=>grouped J.hp J.nonempty J.he J.modes (child z)) (J.normM a t)

theorem site_sound {I : S→Prop} (J : SiteTape p ell k n Mode) (a : ℕ) (t : ℤ)
    (child : Fin n→Mode→Fin 64→SM S (UVBlock J.fw ell))
    (sub : ∀ z m g,Sound I (child z m g) (J.child z m g)) :
    Sound I (siteS J a t child) (J.run a t) :=
  full_sound J.hp J.nonempty J.he J.hk J.nodeM _ _ (J.normM a t)
    (fun z=>grouped_sound J.hp J.nonempty J.he J.modes (child z) (J.child z) (fun m _ g=>sub z m g))
end Physical

#print axioms term_sound
#print axioms prefix_sound
#print axioms full_sound
#print axioms site_sound
end J6R32StatefulArithmetic
