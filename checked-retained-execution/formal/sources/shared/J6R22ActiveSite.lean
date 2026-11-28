import J6R22ActiveBinary
import J6R22ActiveCenter
import J6R22ActiveGrid

/-! The combined finite machine for one centre, on already supplied
ordered descriptors. It takes raw bits/addresses and actual metered
child words, not numeric normalizer coefficients, inverse entries,
interpolation coefficients, or quotient values as inputs. -/
namespace J6R22Active
open scoped BigOperators Polynomial Classical
open Polynomial A1R10 A1R11 A1R12 AOracleMachineTime
open J6ActiveSchedule J6R9Recursive

structure SiteTape (p ell k n : ℕ) (Mode : Type*) where
  hp : 0<p
  hk : 0<k
  he : 0<ell
  fw : List (Word p)
  nonempty : 0<fw.length
  masks : Fin n→Meter {b : List Bool // b.length=fw.length}
  roster : List (ℤ×ℕ)
  modes : List Mode
  child : Fin n→Mode→Fin 64→Meter (UVBlock fw ell)

variable {p ell k n : ℕ} {Mode : Type*}

def SiteTape.nodeM (I : SiteTape p ell k n Mode) (z : Fin n) :
    Meter (UVBlock I.fw ell) :=
  padCost (encodeProbe I.hp I.he (I.masks z).result) (I.masks z).steps

def SiteTape.groupedM (I : SiteTape p ell k n Mode) (z : Fin n) :
    Meter (UVBlock I.fw ell) :=
  groupedProbe I.hp I.nonempty I.he I.modes (I.child z)

def SiteTape.normM (I : SiteTape p ell k n Mode) (a : ℕ) (t : ℤ) :
    Meter (JetTape I.fw ell k) :=
  normalizerM I.hp I.nonempty I.he I.hk a t I.roster

def SiteTape.run (I : SiteTape p ell k n Mode) (a : ℕ) (t : ℤ) :
    Meter (JetTape I.fw ell k) :=
  fullCenterM I.hp I.nonempty I.he I.hk I.nodeM I.groupedM (I.normM a t)

def SiteTape.nodeBill (I : SiteTape p ell k n Mode) : ℕ :=
  ((probeOrder n).map (needsAt I.nodeM)).sum

def SiteTape.childBill (I : SiteTape p ell k n Mode) : ℕ :=
  ((probeOrder n).map (fun z=>probeEntryBill I.modes (I.child z))).sum

def SiteTape.localFee (I : SiteTape p ell k n Mode) (a : ℕ) : ℕ :=
  normalizerFee I.fw.length ell p a k I.hp I.roster+
    n*probeExtra I.fw.length ell p 64 I.modes.length I.hp+
    interpExtra I.fw.length ell p k n I.hp+quotientFee I.fw.length ell p k I.hp+4

theorem SiteTape.nodeM_exact (I : SiteTape p ell k n Mode) {f : ℤ[X]}
    (hF : Modulus p I.hp I.fw=NativeProbeRing.liftPoly p f)
    (fit : n≤2^f.natDegree) (z : Fin n)
    (raw : (I.masks z).result.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree n fit z)) :
    boxTransport hF (nodeMeaning I.hp I.nodeM z)=J6ActiveInterpolation.node p f ell n fit z ∧
    (I.nodeM z).steps=(I.masks z).steps+(I.fw.length*(p+6)+uvWidth I.fw.length ell p+2) := by
  constructor
  · exact encodeProbe_is_literal I.hp I.he hF (I.masks z).result _ raw
  · change (encodeProbe I.hp I.he (I.masks z).result).steps+(I.masks z).steps=_
    rw [encodeProbe_cost]
    omega

theorem SiteTape.normM_exact (I : SiteTape p ell k n Mode) {f : ℤ[X]}
    (hF : Modulus p I.hp I.fw=NativeProbeRing.liftPoly p f)
    (a M u : ℕ) {t : ℤ} (ht : t∈active a M u)
    (hn : (I.roster.map Prod.fst).Nodup)
    (hr : (I.roster.map Prod.fst).toFinset=(active a M u).erase t)
    (ho : ∀ q∈I.roster,q.2=order M u q.1) :
    jetMap (boxTransport hF) k (jetRead I.hp I.nonempty (I.normM a t).result)=
      AdjoinRoot.mk (X^k) ((integralE f ell a M u t).map (reduce p f ell)) ∧
    (I.normM a t).steps≤normalizerFee I.fw.length ell p a k I.hp I.roster := by
  obtain ⟨hm,hc⟩ := normalizerM_exact I.hp I.nonempty I.he I.hk a M u ht I.roster hn hr ho
  refine ⟨?_,hc⟩
  have hR : (boxTransport (ell:=ell) hF).comp (localReduce I.hp I.fw ell)=
      (reduce p f ell).comp (localScalar f ell) :=
    J6ZeroTransport.ringHom_unique _ _
  change jetMap (boxTransport hF) k (jetRead I.hp I.nonempty (normalizerM I.hp I.nonempty I.he I.hk
    a t I.roster).result)=_
  rw [hm,jetMap_mk,Polynomial.map_map,hR,←Polynomial.map_map]
  rfl

theorem SiteTape.interp_bill (I : SiteTape p ell k n Mode) :
    interpBill I.nodeM I.groupedM ≤ I.nodeBill+I.childBill+
      n*probeExtra I.fw.length ell p 64 I.modes.length I.hp := by
  let A := probeOrder n
  let g (z : Fin n) : Meter Unit := ⟨(),needsAt I.nodeM z+(I.groupedM z).steps⟩
  let h (z : Fin n) : Meter Unit := ⟨(),needsAt I.nodeM z+probeEntryBill I.modes (I.child z)⟩
  let b := probeExtra I.fw.length ell p 64 I.modes.length I.hp
  have each (z : Fin n) : (g z).steps≤(h z).steps+b := by
    have hu : (I.groupedM z).steps≤probeEntryBill I.modes (I.child z)+b :=
      (grouped_probe_exact_bill I.hp I.nonempty I.he I.modes (I.child z)).2
    change _≤needsAt I.nodeM z+probeEntryBill I.modes (I.child z)+b
    change needsAt I.nodeM z+(I.groupedM z).steps≤_
    omega
  have hu := bill_mono g h A b (fun z _=>each z)
  have hn : A.length=n := List.length_ofFn
  rw [hn] at hu
  have hsplit (xs : List (Fin n)) :
      (xs.map (fun z=>needsAt I.nodeM z+probeEntryBill I.modes (I.child z))).sum=
      (xs.map (needsAt I.nodeM)).sum+(xs.map (fun z=>probeEntryBill I.modes (I.child z))).sum := by
    induction xs with
    | nil => rfl
    | cons z zs ih => simp only [List.map_cons,List.sum_cons] at *; omega
  have hsum : bill h A=I.nodeBill+I.childBill := hsplit A
  rw [hsum] at hu
  exact hu

set_option maxHeartbeats 1400000 in
theorem SiteTape.exact_local_receipt {d : ℕ} (I : SiteTape p ell k (d+1) Mode)
    {f : ℤ[X]} (hf : f.Monic) (hD : I.fw.length=f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hF : Modulus p I.hp I.fw=NativeProbeRing.liftPoly p f)
    (fit : d+1≤2^f.natDegree)
    (raw : ∀ z,(I.masks z).result.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree _ fit z))
    (a M u : ℕ) {t : ℤ} (ht : t∈active a M u)
    (hn : (I.roster.map Prod.fst).Nodup)
    (hr : (I.roster.map Prod.fst).toFinset=(active a M u).erase t)
    (ho : ∀ q∈I.roster,q.2=order M u q.1) :
    let E := (integralE f ell a M u t).map (reduce p f ell)
    let samples := boxTransport hF ∘ nodeMeaning I.hp I.groupedM
    jetMap (boxTransport hF) k (jetRead I.hp I.nonempty (I.run a t).result)=
      AdjoinRoot.mk (X^k) (J6ActiveNormalizer.quotientJet k E
        (J6ActiveInterpolation.decoded (J6ActiveInterpolation.node p f ell _ fit) samples)) ∧
    (I.run a t).steps≤I.nodeBill+I.childBill+I.localFee a := by
  let E := (integralE f ell a M u t).map (reduce p f ell)
  have hm := I.normM_exact hF a M u ht hn hr ho
  have h := full_center_exact I.hp I.nonempty I.he I.hk hf hD hF fit
    I.nodeM I.groupedM (I.normM a t) E hm.1 (fun z=>(I.nodeM_exact hF fit z (raw z)).1)
  refine ⟨h.1,?_⟩
  have hl := I.interp_bill
  have hb := h.2
  have hN := hm.2
  change (I.run a t).steps ≤ _ at hb
  unfold SiteTape.localFee
  omega

#print axioms SiteTape.nodeM_exact
#print axioms SiteTape.normM_exact
#print axioms SiteTape.interp_bill
#print axioms SiteTape.exact_local_receipt
end J6R22Active


