import V8NativeMessageC3NativeAssemblyN2MainClone

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

/-! The N6 input is one completed MAIN jet on the literal four-clone
unary/edge/implication clause family. Private lists are fixed at its
one public feasible address. The cut is on factor owners, not on the
private-variable groups defining the measurement fibers. -/
namespace V8NativeMessage.N6
open scoped Classical BigOperators Polynomial
open V8NativeMessage.C3.NativeAssembly.MainScan

noncomputable section
variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Finset (W×W)} {r Q J : ℕ}
variable (L : CloneTuple F r Q J)

def pinGroup (v : W) : Fin r := L.factorGroup (.inl v)

abbrev PrivateWord (g : Fin r) := {x : Word L.frame g // eligible L.frame g x}

structure FixedLists where
  count : Fin r → ℕ
  point : ∀ g, Fin (count g) → PrivateWord L g
  weight : ∀ g, Fin (count g) → Jet J

variable (cubic : ∀ v, GraphCutMoments.degree F v=3) (h : feasible L.frame)
variable (P : FixedLists L)

def fullPoint (g : Fin r) (k : Fin (P.count g)) : Clone W → Bool :=
  merge L.frame (repWord L.frame h) g (P.point g k).val

def entry (g : Fin r) (k : Fin (P.count g)) (σ : W→Bool) : Jet J :=
  P.weight g k * nativeGroup F cubic L σ g (fullPoint L h P g k)

def groupJet (g : Fin r) (σ : W→Bool) : Jet J :=
  ∑ k, entry L cubic h P g k σ

def completed (σ : W→Bool) : Jet J := ∏ g, groupJet L cubic h P g σ

def exhaustive : FixedLists L where
  count g := Fintype.card (PrivateWord L g)
  point g := (Fintype.equivFin (PrivateWord L g)).symm
  weight _ _ := 1

theorem exhaustive_completed (σ : W→Bool) :
    completed L cubic h (exhaustive L) σ = (nativeScan F cubic L σ).2.2 := by
  rw [native_value_uses_representatives F cubic L σ h]
  apply Finset.prod_congr rfl
  intro g _
  unfold groupJet entry
  let f : PrivateWord L g → Jet J := fun x =>
    nativeGroup F cubic L σ g (merge L.frame (repWord L.frame h) g x.val)
  change (∑ k : Fin (Fintype.card (PrivateWord L g)),
      (1 : Jet J) * f ((Fintype.equivFin (PrivateWord L g)).symm k)) = _
  simp only [one_mul]
  rw [(Fintype.equivFin (PrivateWord L g)).symm.sum_comp f]
  exact (Finset.sum_subtype ((Finset.univ : Finset (Word L.frame g)).filter (eligible L.frame g))
    (fun x => by simp) (fun x =>
      nativeGroup F cubic L σ g (merge L.frame (repWord L.frame h) g x))).symm

theorem nativeGroup_pin_local (g : Fin r) (x : Clone W→Bool) (σ τ : W→Bool)
    (agree : ∀ v, pinGroup L v=g → σ v=τ v) :
    nativeGroup F cubic L σ g x = nativeGroup F cubic L τ g x := by
  unfold nativeGroup
  apply Finset.prod_congr rfl
  intro c hc
  cases c with
  | inl v =>
    have hv := (Finset.mem_filter.mp hc).2
    simp only [cloneFactor, agree v hv]
  | inr c =>
    cases c <;> rfl

theorem groupJet_pin_local (g : Fin r) (σ τ : W→Bool)
    (agree : ∀ v, pinGroup L v=g → σ v=τ v) :
    groupJet L cubic h P g σ = groupJet L cubic h P g τ := by
  unfold groupJet entry
  apply Finset.sum_congr rfl
  intro k _
  rw [nativeGroup_pin_local L cubic g (fullPoint L h P g k) σ τ agree]

def rowFactor (cut : W→Bool) : Clause F → Bool
  | .inl v => cut v
  | .inr _ => true

def splice (cut : W→Bool) (σ τ : W→Bool) (v : W) : Bool :=
  if cut v then σ v else τ v

def leftPoint (g : Fin r) (k : Fin (P.count g)) (cut : W→Bool) (σ : W→Bool) : Jet J :=
  P.weight g k *
    ∏ c ∈ (Finset.univ : Finset (Clause F)).filter (fun c => L.factorGroup c=g),
      if rowFactor cut c then cloneFactor F cubic L σ (fullPoint L h P g k) c else 1

def rightPoint (g : Fin r) (k : Fin (P.count g)) (cut : W→Bool) (τ : W→Bool) : Jet J :=
    ∏ c ∈ (Finset.univ : Finset (Clause F)).filter (fun c => L.factorGroup c=g),
      if rowFactor cut c then 1 else cloneFactor F cubic L τ (fullPoint L h P g k) c

/-- Split the actual clause factors at one fixed private point. The same
group may own pins on both sides. Non-unary factors are put on the left. -/
theorem point_factors (g : Fin r) (k : Fin (P.count g)) (cut : W→Bool) (σ τ : W→Bool) :
    entry L cubic h P g k (splice cut σ τ) =
      leftPoint L cubic h P g k cut σ * rightPoint L cubic h P g k cut τ := by
  unfold entry nativeGroup leftPoint rightPoint
  rw [mul_assoc, ← Finset.prod_mul_distrib]
  apply congrArg (P.weight g k * ·)
  apply Finset.prod_congr rfl
  intro c _
  cases c with
  | inl v => cases hv : cut v <;> simp [cloneFactor,rowFactor,splice,hv]
  | inr c => cases c <;> simp [cloneFactor,rowFactor]

#print axioms exhaustive_completed
#print axioms nativeGroup_pin_local
#print axioms groupJet_pin_local
#print axioms point_factors

end
end V8NativeMessage.N6
