
import J9R20SameFileAudit
import J9R20SameFileFactors

/-! Quantitative corrected low projection on the very same physical file.
For the printed graph, every one of the four clone columns has a real
port and belongs to the protected set. -/
namespace J9R20SameFile
open scoped BigOperators Classical Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R11Integral J6R10Integral
open J6R14SpecializedBox J8EndToEnd J8Physical LiteralPortCompiler
open J9R14LowPrecisionGeometry J9R14LowPrecisionSlots J9R15FrozenErasurePhysical
open J9R15FrozenErasurePrecision J6R9PacketScopes
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1400000

variable {Packet R S V G : Type} {U : V→Type} {L : ℕ}
variable (d : Layout Packet R S V G U L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G]
variable [(v : V) → Fintype (U v)] [LinearOrder G]
local notation "E" => J8Physical.Wire R
local notation "N" => orientedNetwork d

/-- This records the actual frozen equality columns, not a promise about
an unspecified old table or a free low observation. -/
structure CloneCertificate (F : OldTables d) (n : ℕ) where
  old : Finset (Option (S⊕V))
  typed : ∀ u∈old, ∃ v : V, u=some (.inr v)
  truth : LocalCloneLaw d F old
  port : ∀ u∈old, ∃ e : E, some ((N).col e)=u
  four : old.card=4*n
  wireCount : Fintype.card E=24*n

variable {a : ℕ} (P : PhysicalPacking (orientedNetwork d) a G)
local notation "D" => nativeSeats (fun e : E => P.seat e) (fun e : E => P.seat e)

/-- Certified capacity bounds touches at the positive extreme independently
of endpoint tie-breaking. No enlargement of the footprint is permitted. -/
theorem all_clone_untouched (F : OldTables d) (n : ℕ) (cert : CloneCertificate d F n) :
    (24*(n:ℚ))/6-3*(24*(n:ℚ))/(2^a:ℕ) ≤
      ((kept D cert.old (nativeSeatOwner d P) (((2^a:ℕ):ℤ)-1)).card : ℚ) := by
  letI : DecidableEq (Option (S⊕V)) := fun x y => Classical.propDecidable (x=y)
  have hcap := P.paddedBudget
  rw [← total_slots P.mask,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,cert.wireCount] at hcap
  simpa only [kept, Finset.card_univ] using
    OuterNodePacking.j9_four_clone Finset.univ (rowReal D) (colReal D)
      cert.old (nativeSeatOwner d P) n (show (0:ℕ)<2^a by positivity) cert.four
      (by simpa only [Finset.card_univ] using hcap)

theorem four_clone_same_oriented_low_bits (F : OldTables d) (n : ℕ)
    (cert : CloneCertificate d F n) (sign : S→Bool)
    (f : ℤ[X]) (ell c p q : ℕ) (hf : f.Monic) (hc : 0<c) (hd : 0<f.natDegree)
    (hℓ : 0<ell) (hqp : q≤p)
    (hq : (q:ℚ)≤(24*(n:ℚ))/6-3*(24*(n:ℚ))/(2^a:ℕ))
    (i : Fin a) (ht : (((2^a:ℕ):ℤ)-1)≠0)
    (hv : padicValInt 2 (((2^a:ℕ):ℤ)-1)=i.val)
    (z : Box f ell p) (β : Mode i p P.mask →₀ ℕ) :
    lowerBox p q hqp f ell (actualProjection P i ht hv p z
      (orientedEntryFile d f ell c F sign) hf β)=0 := by
  have hp : ∀ u∈cert.old, ∃ e : E, nativeSeatOwner d P (P.seat e)=u := by
    intro u hu
    obtain ⟨e,he⟩ := cert.port u hu
    exact ⟨e,(nativeSeatOwner_exact d P e).trans he⟩
  exact oriented_file_projection_erases d P cert.old F sign cert.typed cert.truth hp
    f ell c p q hf hc hd hℓ hqp
    (by exact_mod_cast hq.trans (all_clone_untouched d P F n cert)) i ht hv z β

section FourClone
open J7SourceLabels J7PrintedParamsGraph J7ToJ8Incidence
variable {Pair H : Type} [Fintype Pair] [Fintype H]

/-- Extensional clone truth on the actual original ports supplies the
same-file quantitative certificate, without replacing any table. -/
theorem full_source_clone_certificate
    (ends : H×Bool ≃ Pin Pair×Fin 3)
    (d₀ : Layout Packet R (Pin Pair) (PrintedOld Pair H) G (Ports (column ends cycle)) L)
    (F : OldTables d₀) (h : LocalCloneLaw d₀ F (allCloneOwners (Pair:=Pair) (H:=H))) :
    Nonempty (CloneCertificate d₀ F (Fintype.card (Pin Pair))) := by
  refine ⟨⟨allCloneOwners,?_,h,?_,allCloneOwners_card,?_⟩⟩
  · intro u hu
    obtain ⟨x,hx⟩ := (mem_allCloneOwners u).1 hu
    exact ⟨cloneOwner x,hx⟩
  · intro u hu
    obtain ⟨x,rfl⟩ := (mem_allCloneOwners u).1 hu
    obtain ⟨e,he⟩ := allClones_have_literal_port ends x
    let j : Ports (column ends cycle) (cloneOwner x) := ⟨e,he⟩
    exact ⟨ordinaryWire d₀ ⟨cloneOwner x,j⟩,congrArg some (standard_port_owner d₀ _ j)⟩
  · exact (Fintype.card_congr (d₀.column.trans (colWire (column ends cycle)))).trans
      (actual_incidence ends).1

end FourClone
#print axioms all_clone_untouched
#print axioms four_clone_same_oriented_low_bits
#print axioms full_source_clone_certificate

end
end J9R20SameFile
