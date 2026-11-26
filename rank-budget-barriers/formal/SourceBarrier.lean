import ExpanderBarrier
import SourceDensity

/-! Source-layout specialization of the finite barrier. The density cap is
derived from the actual port loads, numerical collision certificate, pin
injection, and ordered-pair coordinate projection. It is not a hypothesis
of the exported source-layout theorem. -/

namespace SourceBarrier

open scoped BigOperators

variable {V P I A J T R S K : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V] [Fintype P]
variable [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype J] [Fintype T]

def labels (pin : V ↪ P) (cell : P → (I → A) × (I → A)) (kept : Finset I)
    (v : V) : kept → A := SourceDensity.firstCoordinates kept (cell (pin v))

/-- Concrete finite layout inputs. A proof that a particular graph-reduction
implementation produces these data is a separate application obligation. -/
structure Geometry (E : Finset (V × V)) (pin : V ↪ P)
    (cell : P → (I → A) × (I → A)) (kept : Finset I)
    (owner : J → kept) (symbols : J → Finset A) where
  delta : ℚ
  certificate : SourceDensity.CollisionCertificate cell delta
  ports : Fintype.card P = 10 * Fintype.card V
  loopless : ∀ v, (v, v) ∉ E
  regular : ∀ v, GraphCutMoments.degree E v = 3
  gamma : ℚ
  eta : ℚ
  H : ℚ
  gamma_pos : 0 < gamma
  gamma_le_one : gamma ≤ 1
  eta_pos : 0 < eta
  eta_le_half : eta ≤ 1 / 2
  H_ge_one : 1 ≤ H
  expansion : ∀ U : Finset V,
    gamma * (min U.card (Fintype.card V - U.card) : ℕ) ≤
      ((GraphCutMoments.boundary E U).card : ℚ)
  balance : ∀ j, eta * Fintype.card V ≤
    (min (EmpiricalCutMoments.labelCut (labels pin cell kept) owner symbols j).card
      (Fintype.card V -
        (EmpiricalCutMoments.labelCut (labels pin cell kept) owner symbols j).card) : ℕ)
  scale : 20 * (∑ i, (ProductVariance.coordinateCount owner i : ℚ) ^ 2) ≤ H ^ 2

variable {E : Finset (V × V)} {pin : V ↪ P}
variable {cell : P → (I → A) × (I → A)} {kept : Finset I}
variable {owner : J → kept} {symbols : J → Finset A}

/-- The density field is proved by finite counting, including the exact size
of the fibers of the projection onto the selected first-side coordinates. -/
def Geometry.toLabelGeometry (G : Geometry E pin cell kept owner symbols) :
    ExpanderBarrier.LabelGeometry E (labels pin cell kept) owner symbols where
  loopless := G.loopless
  regular := G.regular
  densityConstant := 20
  gamma := G.gamma
  eta := G.eta
  H := G.H
  density_nonneg := by norm_num
  density := SourceDensity.source_pin_marginal_twenty pin cell G.delta G.certificate G.ports kept
  gamma_pos := G.gamma_pos
  gamma_le_one := G.gamma_le_one
  eta_pos := G.eta_pos
  eta_le_half := G.eta_le_half
  H_ge_one := G.H_ge_one
  expansion := G.expansion
  balance := G.balance
  scale := G.scale

variable [CommRing R] [CommRing S] [Nontrivial S] [Field K]

/-- From the numerical source-layout certificate to a separated-term lower
bound on a final output with the correct genuine-CNF residue. -/
theorem modular_output_barrier (G : Geometry E pin cell kept owner symbols)
    (d : ℕ) (hd : (d : ℚ) ≤ ExpanderBarrier.margin G.toLabelGeometry)
    (hbudget : ExpanderBarrier.SelectionBudget G.toLabelGeometry)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R) (terms : T → SeparatedRank.VertexTerm V K) (assigned : T → J)
    (hside : ∀ t, (terms t).side =
      EmpiricalCutMoments.labelCut (labels pin cell kept) owner symbols (assigned t))
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) =
      (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S)) :
    2 ^ d ≤ Fintype.card T :=
  ExpanderBarrier.modular_output_barrier G.toLabelGeometry d hd hbudget embed residue
    hinjective output terms assigned hside hrepresentation hcorrect

/-- The same source-layout result with the finite precision reconstruction
identity exposed. No linearity of a residue-representative section is used. -/
theorem reconstructed_output_barrier {U : Type*} [Fintype U]
    (G : Geometry E pin cell kept owner symbols)
    (d : ℕ) (hd : (d : ℚ) ≤ ExpanderBarrier.margin G.toLabelGeometry)
    (hbudget : ExpanderBarrier.SelectionBudget G.toLabelGeometry)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (pi : R) (p : ℕ) (q : U → ℕ) (coefficient : U → K) (cleared : U → R)
    (original replacement error : U → (V → Bool) → R)
    (terms : T → SeparatedRank.VertexTerm V K) (assigned : T → J)
    (hside : ∀ t, (terms t).side =
      EmpiricalCutMoments.labelCut (labels pin cell kept) owner symbols (assigned t))
    (herr : ∀ u σ, replacement u σ = original u σ + pi ^ q u * error u σ)
    (hclear : ∀ u, coefficient u * embed (pi ^ q u) = embed (pi ^ p * cleared u))
    (hexact : ∀ σ, (∑ u, coefficient u * embed (original u σ)) =
      embed (PinnedCNF.modelCount (PinnedCNF.formula E σ) : R))
    (hrepresentation : ∀ σ, (∑ u, coefficient u * embed (replacement u σ)) =
      ∑ t, (terms t).value σ)
    (hpi : residue pi = 0) (hp : 0 < p) :
    2 ^ d ≤ Fintype.card T :=
  ExpanderBarrier.reconstructed_output_barrier G.toLabelGeometry d hd hbudget embed residue
    hinjective pi p q coefficient cleared original replacement error terms assigned hside
    herr hclear hexact hrepresentation hpi hp

#print axioms Geometry.toLabelGeometry
#print axioms modular_output_barrier
#print axioms reconstructed_output_barrier

end SourceBarrier
