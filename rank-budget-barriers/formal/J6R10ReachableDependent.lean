import J6R10ReachableTree
import J6ActiveRun

/-! Specialize finite dependent branching to the actual Appendix D
address carriers. It is crucial that each call/centre chooses its own
finite mode alphabet before any global alphabet is constructed. -/
namespace J6R10Reachable
open J6ActiveRun J6ActiveSchedule

universe uh um
variable {Host : Type uh}

structure NativeShape (Host : Type uh) where
  params : Shape Host Unit
  Mode : ∀ c, Center params c → Type um
  finiteMode : ∀ c t, Fintype (Mode c t)
  decideMode : ∀ c t, DecidableEq (Mode c t)
  weight : ∀ c t, Mode c t → ℕ

variable (N : NativeShape Host)

abbrev NativeMenu (c : Call Host) (t : Center N.params c) : Type um :=
  @Menu (N.Mode c t) (N.finiteMode c t) (N.decideMode c t)
    (registerPrecision N.params c t) (N.weight c t)

abbrev NativeAddress (c : Call Host) :=
  Σ t : Center N.params c, Probe N.params c × NativeMenu N c t × Fin 64

noncomputable def nativeAddressFintype (c : Call Host) : Fintype (NativeAddress N c) := by
  classical
  letI : ∀ t : Center N.params c, Fintype (NativeMenu N c t) :=
    fun t => Finset.fintypeCoeSort (@J6RecursiveMenu.menu (N.Mode c t)
      (N.finiteMode c t) (N.decideMode c t) (registerPrecision N.params c t)
      (N.weight c t))
  unfold NativeAddress
  infer_instance

structure NativeChildren (N : NativeShape Host) where
  host : ∀ c, NativeAddress N c → Host
  edges : ∀ c, NativeAddress N c → ℕ
  bound : ∀ c, N.params.cutoff < c.edges → ∀ w, 32*edges c w ≤ 3*c.edges

variable (B : NativeChildren N)

abbrev LiveAddress (c : Call Host) :=
  {_w : NativeAddress N c // N.params.cutoff < c.edges}

noncomputable def nativePlan : FinitePlan (Call Host) where
  size := fun c => c.edges
  Slot := LiveAddress N
  finiteSlot := fun c => by
    classical
    letI := nativeAddressFintype N c
    infer_instance
  child := fun c w =>
    ⟨B.host c w.val,c.depth+1,B.edges c w.val,registerPrecision N.params c w.val.1⟩
  smaller := fun c w =>
    (child_shrinks _ _ (Nat.zero_lt_of_lt w.property) (B.bound c w.property w.val)).2

variable (root : Call Host)

abbrev Envelope :=
  Alphabet (nativePlan N B) root (Center N.params) N.Mode

noncomputable instance envelopeFinite : Fintype (Envelope N B root) := by
  letI : ∀ c (t : Center N.params c), Fintype (N.Mode c t) := N.finiteMode
  unfold Envelope
  infer_instance

noncomputable def envelopeAt (c : Call Host) (hc : NativeReach (nativePlan N B) root c)
    (t : Center N.params c) : N.Mode c t ↪ Envelope N B root :=
  nativeMode (nativePlan N B) root (Center N.params) N.Mode c hc t

noncomputable def paddedShape : Shape Host (Envelope N B root) where
  cutoff := N.params.cutoff
  levelWidth := N.params.levelWidth
  levelBits := N.params.levelBits
  weight := fun c t j => by
    classical
    exact if hc : NativeReach (nativePlan N B) root c then
      if ht : t ∈ active (N.params.levelBits c.depth) c.edges (N.params.levelWidth c.depth) then
        let τ : Center N.params c := ⟨t,ht⟩
        paddedWeight (registerPrecision N.params c τ) (envelopeAt N B root c hc τ) (N.weight c τ) j
      else 1
    else 1

theorem paddedShape_weight (c : Call Host) (hc : NativeReach (nativePlan N B) root c)
    (t : Center N.params c) :
    (paddedShape N B root).weight c t.val =
      paddedWeight (registerPrecision N.params c t) (envelopeAt N B root c hc t) (N.weight c t) := by
  classical
  funext j
  simp only [paddedShape,dif_pos hc,dif_pos t.property]

variable [DecidableEq (Envelope N B root)]

/-- At a genuine active site the generated widened mode slots are exactly
the actual dependent native slots, with no additional legal exponent. -/
noncomputable def nativeSlotEquiv (c : Call Host)
    (hc : NativeReach (nativePlan N B) root c) (ha : N.params.cutoff < c.edges)
    (t : Center N.params c) (hw : ∀ i, 0 < N.weight c t i) :
    NativeMenu N c t ≃ Modes (paddedShape N B root) c t := by
  letI : Fintype (N.Mode c t) := N.finiteMode c t
  letI : DecidableEq (N.Mode c t) := N.decideMode c t
  let p := registerPrecision N.params c t
  have hp : 0 < p := (Nat.zero_le c.prec).trans_lt
    (child_monotone c.prec _ _ _ t.val (Nat.zero_lt_of_lt ha))
  let eq := menuEquiv p hp (envelopeAt N B root c hc t) (N.weight c t) hw
  have htype : Menu p (paddedWeight p (envelopeAt N B root c hc t) (N.weight c t)) =
      Modes (paddedShape N B root) c t :=
    congrArg (fun w : Envelope N B root → ℕ => Menu p w) (paddedShape_weight N B root c hc t).symm
  exact eq.trans (Equiv.cast htype)

#print axioms nativePlan
#print axioms envelopeAt
#print axioms paddedShape_weight
#print axioms nativeSlotEquiv
end J6R10Reachable