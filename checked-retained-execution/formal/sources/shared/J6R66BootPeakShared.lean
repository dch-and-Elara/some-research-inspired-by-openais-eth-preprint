import J6R66BootPeakRequest
import J6R55SelectedPeakBootWriter

/-! Select the actual immutable fields kept in the R57 image. In
particular, the prescribed positive-probe bank is a closure over the
actual R27 tape; this proof names that data and the exact read. -/
namespace J6R66.BootPeak
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6Mesh J6OrientedHost J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot
open J6R28GeneratedRootFrame J6R27PrescribedProbe J6R54PublicFamily J6R27OriginalGate
open J6R35GatewayPreparation J6R57PublicRequest J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R17ModeTape J6R32RootGeneratedRegistryInputs J6R54PeakInput J6R55SelectedPeak J6R24MeteredRecursion
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 3800
set_option Elab.async false

def flagBits : OldFlag→List Bool
  | .literal pos => [true,pos]
  | .equal => [false,true]
  | .free => [false,false]

def literalPortBits {r c d : ℕ} (u : SignedHalfPort r c d) : List Bool :=
  u.row.val++u.column.val++u.leg.val++[u.side]++flagBits u.flag

theorem literal_port_width {r c d : ℕ} (u : SignedHalfPort r c d) :
    (literalPortBits u).length=r+c+d+3 := by
  have f : (flagBits u.flag).length=2 := by cases u.flag <;> rfl
  simp only [literalPortBits,List.length_append,u.row.property,u.column.property,u.leg.property,
    List.length_cons,List.length_nil,f]

def pageRefBits {q : ℕ} (P : PageRef q) : List Bool :=
  P.labels.1++P.labels.2++P.copy.bits

def maskRowBits {q : ℕ} (R : MaskRow q) : List Bool := pageRefBits R.address++R.bits

def modeRowBits {q : ℕ} (R : RawMode q) : List Bool :=
  R.key.1++R.key.2++R.page.bits++R.tile.bits++R.weight.bits

def residentSourceBits {m q : ℕ} (D : Resident m q) : ℕ :=
  D.axis.length+bitSize physicalSeatBits D.seats+bitSize maskRowBits D.mask+
    bitSize modeRowBits D.roster.modes+bitSize Word.bits D.roster.weights+
    D.roster.precision.bits.length

section Root
noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew)
variable (I : SharedInputs G ell q rr cc dd prec kp bw)

def sharedRequestBits : ℕ :=
  let J := (buildRequestImage W I).result
  let D := J.tables.root
  bitSize entryBits J.tables.requests.rows+
    bitSize literalPortBits J.compiled.literal.raw+
    bitSize Subtype.val J.compiled.frame.words+
    J.compiled.regs.copies.bits.length+J.compiled.regs.pre.bits.length+
    J.compiled.regs.birth.bits.length+J.compiled.codeTape.bits.length+J.compiled.mark.bits.length+
    residentSourceBits D.resident+bitSize physicalPortWords D.parents+
    bitSize Subtype.val (positiveTape f.natDegree (literalDegree m native+1)).result

theorem actual_image_probe_word_is_read_from_counted_tape :
    let J := (buildRequestImage W I).result
    let H := positiveTape f.natDegree (literalDegree m native+1)
    ∃ pos : 0<f.natDegree,
      bitSize Subtype.val H.result=(literalDegree m native+1)*f.natDegree ∧
      ∀ j : Fin (literalDegree m native+1),J.tables.requests.probes.read j=readTape pos H.result j := by
  let spare : literalDegree m native+1<2^f.natDegree :=
    literal_external_spare f ell m (printedHalf m) n base native (printedRankWidth m)
      T (constantRootWord m) G
  have pos := positive_width_of_fit f.natDegree (literalDegree m native) spare
  obtain ⟨exactTape,_⟩ := positive_tape_exact f.natDegree (literalDegree m native+1) pos spare
  refine ⟨pos,?_,?_⟩
  · change bitSize Subtype.val (positiveTape f.natDegree (literalDegree m native+1)).result=_
    rw [bitSize_exact _ _ _ (fun w : A1R10.Word f.natDegree => w.property),exactTape,List.length_ofFn]
  · intro j
    rfl

theorem actual_shared_image_field_census :
    let J := (buildRequestImage W I).result
    sharedRequestBits W I=
      publicCount m native*entryWidth kp tc tj tw+
      m*(rr+cc+dd+3)+f.natDegree*J6SourcePrecision.printed m base+
      q+q+prec+bw+kp+
      residentSourceBits J.tables.root.resident+bitSize physicalPortWords J.tables.root.parents+
      (literalDegree m native+1)*f.natDegree := by
  let J := (buildRequestImage W I).result
  have rawLen : J.compiled.literal.raw.length=m := by
    rw [J.compiled.literal.exactFile,List.length_ofFn]
  have fieldLen : J.compiled.frame.words.length=f.natDegree :=
    J.compiled.frame.natDegree J.compiled.hf
  obtain ⟨_,probe,_⟩ := actual_image_probe_word_is_read_from_counted_tape W I
  change bitSize entryBits J.tables.requests.rows+bitSize literalPortBits J.compiled.literal.raw+
    bitSize Subtype.val J.compiled.frame.words+
    J.compiled.regs.copies.bits.length+J.compiled.regs.pre.bits.length+
    J.compiled.regs.birth.bits.length+J.compiled.codeTape.bits.length+J.compiled.mark.bits.length+
    residentSourceBits J.tables.root.resident+bitSize physicalPortWords J.tables.root.parents+
    bitSize Subtype.val (positiveTape f.natDegree (literalDegree m native+1)).result=_
  rw [show bitSize entryBits J.tables.requests.rows=_ from actual_request_image_has_exact_catalogue_bits W I,
    bitSize_exact _ _ _ literal_port_width,rawLen,
    bitSize_exact _ _ _ (fun w : A1R10.Word (J6SourcePrecision.printed m base) => w.property),fieldLen,
    J.compiled.regs.copies.size,J.compiled.regs.pre.size,J.compiled.regs.birth.size,
    J.compiled.codeTape.size,J.compiled.mark.size,probe]

#print axioms literal_port_width
#print axioms sharedRequestBits
#print axioms actual_image_probe_word_is_read_from_counted_tape
#print axioms actual_shared_image_field_census
end
end Root
end J6R66.BootPeak
