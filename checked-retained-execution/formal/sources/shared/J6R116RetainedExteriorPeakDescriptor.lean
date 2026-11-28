import J6R34RootAtlasStable

/-! Selected encoded words of the single physical exterior descriptor.
The shared graph/frame and the already published header/atlas are not
encoded a second time by this observer. -/
namespace J6R116RetainedExteriorPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6OrientedHost
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R31RootResidentTables
open J6R34RootAtlas J6R28GeneratedRootFrame J6R32RootGeneratedRegistryInputs
open J6R30ProducedGateRegistry J6R21Ancestor

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9000000
set_option maxRecDepth 4350
set_option Elab.async false

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)

/-- Literal address words, issuer word, birth precision, two physical
register words and the signed context. One sign bit is included. -/
def descriptorBits : ℕ :=
  X.address.centre.bits.length+X.address.sample.bits.length+X.address.group.bits.length+
    X.issue.result.bits.length+X.birth.bits.length+X.copies.bits.length+X.pre.bits.length+
      1+X.context.magnitude.bits.length+X.context.codeWidth.bits.length

theorem actual_retained_descriptor_count_is_its_word_widths :
    descriptorBits X = (tc+tj+6)+key+prec+2*q+1+tw+bw := by
  unfold descriptorBits
  rw [X.address.centre.size,X.address.sample.size,X.address.group.size,
    X.issue.result.size,X.birth.size,X.copies.size,X.pre.size,X.context.magnitude.size,X.context.codeWidth.size]
  omega

#print axioms descriptorBits
#print axioms actual_retained_descriptor_count_is_its_word_widths
end J6R116RetainedExteriorPeak

