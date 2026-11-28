import V8NativeMessageN8LiteralChart
import V8NativeMessageN7Public

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000
set_option maxRecDepth 2400

/-! Source D lines 340–344 require the printed number of distinct
binary-coordinate lifts, not one enumerator. Keep the frozen physical
graph, chart, creation file, center and legal mode; choose only the
extension-field binary word at each prescribed probe address. -/
namespace V8NativeMessage.N8Prescribed
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
open J6ActiveRun J6R12Blueprint J6R11Blueprint
open Paper5.D1Literal Paper5.HybridClosure V8NativeMessage.N6D V8NativeMessage.N7
open V8NativeMessage.N8Literal

noncomputable section
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "r*" => (oldRowRoot F reg f (fun _=>false))

/-- A sign-independent table per retained center, with the original
printed number of addresses. An embedding picks those residues without
repetition from the full binary-coordinate menu. The zero word is
allowed (at most once in a row, by injectivity). -/
abbrev Chart (i : rootKept F f) :=
  (t : Centers F reg i)→PublicProbe F reg f ↪ (Fin f.natDegree→Bool)

variable (d : N6PublicReady F reg (f:=f)) (i : rootKept F f)

def frozenChart : Chart F reg i := fun _ =>
  ⟨NativeProbeRing.chosenRep f.natDegree _ d.fit,NativeProbeRing.chosenRep_injective _ _ d.fit⟩

variable (B : Chart F reg i)

def prescribedNode (t : Centers F reg i) (z : PublicProbe F reg f) :
    Residue f 1 (sitePrecision F reg t.val) :=
  let p := sitePrecision F reg t.val
  J6ActiveInterpolation.scalarIn p f 1 (NativeProbeRing.probe p f (B t z))

theorem frozen_probe_is_original (t : Centers F reg i) (z : PublicProbe F reg f) :
    prescribedNode F reg i (frozenChart F reg d i) t z = siteProbe F reg d t.val z := rfl

theorem prescribed_binary_residues_distinct (hf : f.Monic) (hd : 0<f.natDegree)
    (t : Centers F reg i) :
    let p := sitePrecision F reg t.val
    Function.Injective (fun z : PublicProbe F reg f =>
      NativeProbeRing.residueMap p (register_positive d t.val) f (NativeProbeRing.probe p f (B t z))) :=
  (NativeProbeRing.binary_residues_injective _ (register_positive d t.val) f hf hd).comp (B t).injective

include d in
theorem prescribed_pair_units (hf : f.Monic) (hd : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] (t : Centers F reg i)
    (z z' : PublicProbe F reg f) (h : z≠z') :
    IsUnit (prescribedNode F reg i B t z'-prescribedNode F reg i B t z) := by
  let p := sitePrecision F reg t.val
  let hp := register_positive d t.val
  have hu : IsUnit (NativeProbeRing.probe p f (B t z')-NativeProbeRing.probe p f (B t z)) := by
    apply NativeProbeRing.unit_of_residue p hp f hf
    rw [map_sub,sub_ne_zero]
    exact fun same=>h ((prescribed_binary_residues_distinct F reg d i B hf hd t) same).symm
  change IsUnit ((J6ActiveInterpolation.scalarIn p f 1) (NativeProbeRing.probe p f (B t z'))-
    (J6ActiveInterpolation.scalarIn p f 1) (NativeProbeRing.probe p f (B t z)))
  rw [← map_sub]
  exact hu.map (J6ActiveInterpolation.scalarIn p f 1)

theorem prescribed_zero_word_is_zero (t : Centers F reg i) (z : PublicProbe F reg f)
    (isZero : B t z=fun _=>false) : prescribedNode F reg i B t z=0 := by
  simp [prescribedNode,isZero,NativeProbeRing.probe,NativeProbeRing.binaryPoly]

variable (P : RootPacking F reg f)

def prescribedGroupReply (hf : f.Monic) (σ : W→Bool)
    (t : Centers F reg i) (z : PublicProbe F reg f) (β : PublicMenu F reg f P d t.val) (g : Fin 64) :
    Residue f 1 (sitePrecision F reg t.val) :=
  let p := sitePrecision F reg t.val
  reduce p f 1 ((actualPacketHost P (PublicIndex F reg f d t.val) (centerNonzero t.val) rfl
    p (J6R10Integral.box_two_nil p f 1) (prescribedNode F reg i B t z)
    (oldRowFile F reg f (4*Fintype.card W+1) σ) β.val g).contract hf)

def prescribedWhole (hf : f.Monic) (σ : W→Bool)
    (t : Centers F reg i) (z : PublicProbe F reg f) (β : PublicMenu F reg f P d t.val) :
    Residue f 1 (sitePrecision F reg t.val) :=
  ∏ g : Fin 64, prescribedGroupReply F reg d i B P hf σ t z β g

theorem prescribed_product_is_source (hf : f.Monic) (σ : W→Bool)
    (t : Centers F reg i) (z : PublicProbe F reg f) (β : PublicMenu F reg f P d t.val) :
    let p := sitePrecision F reg t.val
    prescribedWhole F reg d i B P hf σ t z β =
      V8PooledMenu.slot P (PublicIndex F reg f d t.val) (centerNonzero t.val) rfl
        p (J6R10Integral.box_two_nil p f 1) (prescribedNode F reg i B t z)
        (oldRowFile F reg f (4*Fintype.card W+1) σ) hf β.val := rfl

theorem frozen_group_is_original (hf : f.Monic) (σ : W→Bool)
    (t : Centers F reg i) (z : PublicProbe F reg f) (β : PublicMenu F reg f P d t.val) (g : Fin 64) :
    prescribedGroupReply F reg d i (frozenChart F reg d i) P hf σ t z β g =
      publicReply F reg f P d hf σ ⟨t.val,z,β,g⟩ :=
  (public_word_is_literal F reg P d hf ⟨t.val,z,β,g⟩ σ).symm

theorem frozen_product_is_original (hf : f.Monic) (σ : W→Bool)
    (t : Centers F reg i) (z : PublicProbe F reg f) (β : PublicMenu F reg f P d t.val) :
    prescribedWhole F reg d i (frozenChart F reg d i) P hf σ t z β =
      wholePublic F reg P d hf σ ⟨t.val,z,β⟩ := by
  exact Finset.prod_congr rfl (fun g _=>frozen_group_is_original F reg d i P hf σ t z β g)

#print axioms frozen_probe_is_original
#print axioms prescribed_binary_residues_distinct
#print axioms prescribed_pair_units
#print axioms prescribed_zero_word_is_zero
#print axioms prescribed_product_is_source
#print axioms frozen_group_is_original
#print axioms frozen_product_is_original
end
end V8NativeMessage.N8Prescribed