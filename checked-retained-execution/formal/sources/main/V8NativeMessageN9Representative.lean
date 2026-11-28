import V8NativeMessageN9Semantic
import V8NativeMessageN9Lower

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-! A functional one-form observation is a true reachable native
observation, up to replacement by one legal singleton at the same
graph-fixed public probe. No additional values for unrequested modes
are needed to extend the row lower bound. -/
namespace V8NativeMessage
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
open V8PooledMenu J6RecursiveMenu J6R10RowAffine
noncomputable section

section One
variable {E A B G S : Type} [LinearOrder G] [Fintype G] [CommRing S]
  {a p : ℕ} {N : Network E A B} (P : PhysicalPacking N a G) (i : Fin a)

theorem admissible_singleton
    (β : Mode i p P.mask→₀ℕ) (hβ : β∈menu p (weight i p P.mask))
    (m : Mode i p P.mask) (hm : β m≠0) :
    Finsupp.single m 1 ∈ menu p (weight i p P.mask) := by
  have hw (n : Mode i p P.mask) : 0<weight i p P.mask n := by simp [weight]
  rw [exact_printed_menu p _ hw] at hβ ⊢
  apply lt_of_le_of_lt _ hβ
  have hsingle : weighted (weight i p P.mask) (Finsupp.single m 1)=weight i p P.mask m := by
    unfold weighted
    rw [Finset.sum_eq_single m]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
    · intro hn
      exact (hn (Finset.mem_univ m)).elim
  rw [hsingle]
  have he : 1 ≤ β m := Nat.one_le_iff_ne_zero.mpr hm
  have hhead : weight i p P.mask m ≤ weight i p P.mask m * β m := by
    simpa using Nat.mul_le_mul_left (weight i p P.mask m) he
  exact hhead.trans
    (Finset.single_le_sum (fun j _ => Nat.zero_le (weight i p P.mask j * β j)) (Finset.mem_univ m))

theorem zero_mode_tagged (g : G) :
    RestrictedChild P i (0 : Mode i p P.mask→₀ℕ) g := by
  right
  intro m n hm
  exact (hm.2 rfl).elim

theorem singleton_mode_tagged (m : Mode i p P.mask) (g : G) :
    RestrictedChild P i (Finsupp.single m 1) g := by
  right
  have unique (n : Mode i p P.mask) (hn : SourceActive P i (Finsupp.single m 1) g n) : n=m := by
    by_contra h
    exact hn.2 (by simp [Ne.symm h])
  intro n r hn hr
  rw [unique n hn,unique r hr]

theorem decode_zero (g : G) (tape : ChildTape P i) (hc : (2:S)=0) :
    decodeChild P i (0 : Mode i p P.mask→₀ℕ) g tape hc = parityMap hc (tape.1 g) := by
  simp [decodeChild,TargetActive,SourceActive]

theorem decode_single_source (g : G) (m : Mode i p P.mask) (h : (childSource P i m).1=g)
    (tape : ChildTape P i) (hc : (2:S)=0) :
    decodeChild P i (Finsupp.single m 1) g tape hc = parityMap hc (tape.2 (modeForm P i m)) := by
  have he (n : Mode i p P.mask) (hn : (Finsupp.single m 1 : _→₀ℕ) n≠0) : n=m := by
    by_contra hne
    exact hn (by simp [Ne.symm hne])
  have ht : ¬ TargetActive P i (Finsupp.single m 1) g := by
    rintro ⟨n,hn,ha⟩
    rw [he n ha] at hn
    exact source_distinct P.mask i m (hn.trans h.symm)
  have hs : ∃ n, SourceActive P i (Finsupp.single m 1) g n := ⟨m,h,by simp⟩
  rw [decodeChild,if_neg ht,dif_pos hs,he _ hs.choose_spec.2]

end One
namespace Five
open V8PooledMenu.FiveCopy V8PooledRange V8PooledRange.NativeOrigin
variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}
variable (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V) (t : Site V)
local notation "idx" => (rootIndex hu huM t)

abbrev SemanticChildAddress :=
  {q : Address P hu huM t × Fin 64 // RestrictedSemantic P idx q.1.beta q.2}

private def zero_address (q : Address P hu huM t) : Address P hu huM t :=
  ⟨q.probeIdx,0,zero_in_menu _ (lt_of_lt_of_le Nat.zero_lt_one
      (precision_fits hu huM (parityPrecision V) t)) _ (fun n => by simp [weight])⟩

private def single_address (q : Address P hu huM t) (m : Mode idx (high t) P.mask)
    (hm : q.beta m≠0) : Address P hu huM t :=
  ⟨q.probeIdx,Finsupp.single m 1,admissible_singleton P idx q.beta q.legal m hm⟩

def relevantRepresentative (q : Address P hu huM t) (g : Fin 64) :
    ChildAddress P hu huM t :=
  if ht : TargetActive P idx q.beta g then ⟨(q,g),Or.inl ht⟩
  else if h : ∃ m, SourceActive P idx q.beta g m then
    ⟨(single_address P hu huM t q h.choose h.choose_spec.2,g),
      singleton_mode_tagged P idx h.choose g⟩
  else ⟨(zero_address P hu huM t q,g),zero_mode_tagged P idx g⟩

theorem N9_representative (probes : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree)
    (s : V→Bool) (q : SemanticChildAddress P hu huM t) :
    rawParityChild P hu huM t probes hf s q.val.1 q.val.2 =
      actualChildMenu P hu huM t probes hf s
        (relevantRepresentative P hu huM t q.val.1 q.val.2) := by
  rw [N9_semantic_native P hu huM t probes hf hd s _ _ q.property,
    N9_native P hu huM t probes hf hd s]
  unfold decodeNativeChildren relevantRepresentative
  by_cases ht : TargetActive P idx q.val.1.beta q.val.2
  · rw [dif_pos ht]
  · rw [dif_neg ht]
    by_cases hs : ∃ m, SourceActive P idx q.val.1.beta q.val.2 m
    · rw [dif_pos hs]
      change decodeChild P idx q.val.1.beta q.val.2 _ _ =
        decodeChild P idx (Finsupp.single hs.choose 1) q.val.2 _ _
      rw [decode_single_source P idx q.val.2 hs.choose hs.choose_spec.1,decodeChild,if_neg ht,dif_pos hs]
    · rw [dif_neg hs]
      change decodeChild P idx q.val.1.beta q.val.2 _ _ =
        decodeChild P idx (0 : Mode idx (high t) P.mask→₀ℕ) q.val.2 _ _
      rw [decode_zero P idx q.val.2,decodeChild,if_neg ht,dif_neg hs]

#print axioms admissible_singleton
#print axioms singleton_mode_tagged
#print axioms decode_single_source
#print axioms N9_representative
end Five
end
end V8NativeMessage