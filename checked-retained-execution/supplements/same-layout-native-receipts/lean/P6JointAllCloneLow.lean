import J9R20SameFileCatalog
import P9BalancedChart

namespace Paper6JointSeating
open scoped Classical Polynomial BigOperators
open P11FullPacking OuterNodePacking J6R10Repack
open J9R20SameFile J9R14LowPrecisionGeometry J9R15FrozenErasurePhysical
open J9R15FrozenErasurePrecision J6R14SpecializedBox J6R9PacketScopes J6R9Recursive
open J8Physical J8EndToEnd Polynomial

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000

variable {Packet R S V G : Type} {U : V→Type} {L : ℕ}
variable (d : Layout Packet R S V G U L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G]
variable [(v : V) → Fintype (U v)] [LinearOrder G]
variable {a : ℕ} (P : PhysicalPacking (orientedNetwork d) a G)

local instance (priority := 21000) ownerDecEq : DecidableEq (Option (S⊕V)) :=
  fun x y => Classical.propDecidable (x=y)
local instance (priority := 21000) pageDecEq : DecidableEq (Page a P.copies G) :=
  fun x y => Classical.propDecidable (x=y)
local notation "E" => J8Physical.Wire R
local notation "D" => nativeSeats (fun e : E => P.seat e) (fun e : E => P.seat e)
local notation "OWN" => nativeSeatOwner d P

theorem all_clone_guard_card_le_kept (old guard : Finset (Option (S⊕V))) (hg : guard ⊆ old)
    (s : Bool) (n : ℤ) (hn : if s then n < 0 else 0 < n)
    (reserved : ∀ e : E, some ((orientedNetwork d).col e) ∈ guard →
      (P.seat e).2.val = GuardedPacking.endpoint (2^a) s) :
    guard.card ≤ (kept D old OWN n).card := by
  apply Finset.card_le_card
  intro u hu
  unfold kept untouched
  refine Finset.mem_sdiff.mpr ⟨hg hu,?_⟩
  intro hi
  obtain ⟨slot,hmat,hown⟩ := Finset.mem_image.mp hi
  have hreal := (mem_matchedColumns _ _ _ _ _).mp hmat |>.2.1
  simp only [colReal, decide_eq_true_eq] at hreal
  obtain ⟨e,he⟩ := hreal
  change P.seat e = slot at he
  subst slot
  rw [nativeSeatOwner_exact] at hown
  exact P11SourceGeometry.endpoint_not_matched _ _ _ s n hn _ (reserved e (hown ▸ hu)) hmat

/-- Actual receiver restriction on every nonzero signed center, without
restricting the original probe or native-precision mode. The certificate
records the actual frozen trivalent equality columns of the original file. -/
theorem actual_all_clone_nonzero_menu_zero
    (F : OldTables d) (N : ℕ) (cert : CloneCertificate d F N) (sign : S→Bool)
    (gs : Bool → Finset (Option (S⊕V))) (hgs : ∀ s, gs s ⊆ cert.old)
    (reserved : ∀ s, ∀ e : E, some ((orientedNetwork d).col e) ∈ gs s →
      (P.seat e).2.val = GuardedPacking.endpoint (2^a) s)
    (f : ℤ[X]) (ell c q : ℕ) (hf : f.Monic) (hc : 0<c) (hd : 0<f.natDegree)
    (hℓ : 0<ell) (hq : ∀ s, q≤(gs s).card) :
    ∀ (n : ℤ) (hn : n≠0) (i : Fin a) (hv : padicValInt 2 n=i.val)
        (p : ℕ) (hqp : q≤p) (z : Box f ell p) (β : Mode i p P.mask →₀ ℕ),
      lowerBox p q hqp f ell (actualProjection P i hn hv p z
        (orientedEntryFile d f ell c F sign) hf β)=0 := by
  intro n hn i hv p hqp z β
  have hports : ∀ u∈cert.old, ∃ e : E, OWN (P.seat e)=u := by
    intro u hu
    obtain ⟨e,he⟩ := cert.port u hu
    exact ⟨e,(nativeSeatOwner_exact d P e).trans he⟩
  have hz : q ≤ (kept D cert.old OWN n).card := by
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · exact (hq true).trans (all_clone_guard_card_le_kept d P cert.old (gs true) (hgs true)
        true n hneg (reserved true))
    · exact (hq false).trans (all_clone_guard_card_le_kept d P cert.old (gs false) (hgs false)
        false n hpos (reserved false))
  exact oriented_file_projection_erases d P cert.old F sign cert.typed cert.truth hports
    f ell c p q hf hc hd hℓ hqp hz i hn hv z β

#print axioms all_clone_guard_card_le_kept
#print axioms actual_all_clone_nonzero_menu_zero
end
end Paper6JointSeating


