import J6R49LiveLiteralRun
import J6R49CostRuntime

/-! A single source-faithful run has the decoded source answer, restored
directory and the printed scoped time bound. The local raw tariff
hypotheses are deliberately explicit, not consequences of value validity. -/
namespace J6R50Integration
open scoped Polynomial BigOperators
open J6Mesh J6OrientedHost J6R21Ancestor J6R32RootGeneratedRegistryInputs J6R31RootResidentTables
open J6R34RootAtlas J6R35RootOrigins J6R33StatefulArithmeticPage J6R32StatefulArithmetic
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26StablePreparedRoot J6R24MeteredRecursion J6R48DFS J6R49DFS J6R49Leaf
open J6R30GeneratedRootLayout J6R27OriginalGate J6R24LegalLayout J6R10Repack
open J6R49LiveBits J6R49Cost J6R16ModeCost J6R12Blueprint

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 3200

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw s C streamQ : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (pad : ℕ)
variable (I : InputFamily T key prec tw bw (pageKeyWidth m+pad))
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem occurrence_size_drops {Y : Type*} (F : FinitePlan Y) (a : Y)
    (k : ℕ) (y : Y) (hy : y∈occurrences F a k) :
    F.size y+k≤F.size a := by
  induction k generalizing y with
  | zero =>
    simp only [occurrences,List.mem_singleton] at hy
    subst y
    simp
  | succ k ih =>
    rw [occurrences,List.mem_flatMap] at hy
    obtain ⟨parent,hPar,hChild⟩ := hy
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp hChild
    have hs := F.smaller parent w
    have hn := ih parent hPar
    omega

theorem no_occurrences_after_size {Y : Type*} (F : FinitePlan Y) (a : Y) :
    occurrences F a (F.size a+1)=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro y h
  have impossible := occurrence_size_drops F a (F.size a+1) y h
  omega

theorem stable_path_depth_bound_from_start {f' : ℤ[X]} {ell' s' C' : ℕ}
    (cfg' : RootBounds s' C' f')
    (sel' : Selector (printedParams (f:=f') (ell:=ell') s') (sourceDelta s'))
    {start finish : Call (PhysicalHost f' ell')}
    (walk : NativeReach (Plan sel') start finish)
    (stable : Stable s' C' start) (startFit : start.depth≤pathLimit s' C') :
    finish.depth≤pathLimit s' C' := by
  let F (x : Call (PhysicalHost f' ell')) := Stable s' C' x ∧ x.depth≤pathLimit s' C'
  have hStep (x : Call (PhysicalHost f' ell')) (hx : F x) (w : (Plan sel').Slot x) :
      F ((Plan sel').child x w) := by
    have ha : J9PrintedSchedule.leafThreshold s' (Nat.clog 2 s')<x.edges := w.property
    have hLam : 0<Nat.clog 2 s' :=
      (by decide : 0<(1024:ℕ)).trans_le (root_lambda_large cfg')
    have H := active_depth_power s' (Nat.clog 2 s') C' x.edges x.depth hLam ha hx.1.sizeByDepth
    have hD := Nat.le_log_of_pow_le (by decide : 1<(8:ℕ)) H
    exact ⟨stable_step cfg' sel' hx.1 w,Nat.succ_le_succ hD⟩
  exact (nativeReach_run_invariant (Plan sel') F hStep walk ⟨stable,startFit⟩).2

omit [Fact (Irreducible (NativeProbeRing.residuePoly f))] in
theorem literal_exterior_depth_one : (exteriorChild G ell X.centre X.sample X.group).depth = 1 := rfl

theorem literal_run_value_and_cost (basePos : 0<base) (hq : 0<streamQ)
    (ord : ∀ {c : Call (PhysicalHost f ell)},
      Path sel (exteriorChild G ell X.centre X.sample X.group) c → Fin c.edges ≃ c.host.Edge)
    (A : ∀ {c : Call (PhysicalHost f ell)}
      (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
      (h : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges),
      ActiveMachine sel (ready_reachable cfg sel p.reached T.rootStable h) T.bank streamQ)
    (retire : PageJob f ell key prec tw bw (pageKeyWidth m+pad) → ℕ)
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (origin : IsLive (X.seed pad) initial)
    (valid : ReadyOnStack (compileFamily I) initial)
    :
    let ext := exteriorChild G ell X.centre X.sample X.group
    let run := nativeStream
      (canonicalStreaming (literalLeafStreaming X pad I basePos hq ord A)) retire ext .root initial
    (T.frame (NativeReach.reflexive ext)).decode run.result.1 =
        (sourceBlueprint sel ext X.hf).program.run ext ∧ run.result.2=initial ∧
      run.steps ≤ ∑ j∈Finset.range (pathLimit s C+1),
        levelBill (nativeScopedPlan sel ext) ⟨ext,Path.root⟩
          (actualStreamOwn (canonicalStreaming (literalLeafStreaming X pad I basePos hq ord A))
            retire initial) j := by
  let ext := exteriorChild G ell X.centre X.sample X.group
  let R := canonicalStreaming (literalLeafStreaming X pad I basePos hq ord A)
  let Q := nativeScopedPlan sel ext
  let root : Sigma (Path sel ext) := ⟨ext,Path.root⟩
  obtain ⟨value,restore⟩ := original_stream_with_literal_stopping_words X pad I
    basePos hq ord A retire initial origin valid
  refine ⟨value,restore,?_⟩
  have hStart : ext.depth≤pathLimit s C := by
    rw [literal_exterior_depth_one X]
    unfold pathLimit
    omega
  have term : occurrences Q root (pathLimit s C+1)=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro z hz
    have hp : z.1∈(occurrences Q root (pathLimit s C+1)).map Sigma.fst :=
      List.mem_map_of_mem hz
    change z.1∈(occurrences (scopePlan (Plan sel) (Path sel ext)
      (fun x w=>Path.step x.2 w)) root (pathLimit s C+1)).map Sigma.fst at hp
    rw [scope_occurrences_project] at hp
    obtain ⟨reach,dep⟩ := occurrence_reach_depth (Plan sel) (fun c=>c.depth)
      (fun _ _=>rfl) ext (pathLimit s C+1) z.1 hp
    have cap := stable_path_depth_bound_from_start cfg sel reach T.rootStable hStart
    omega
  exact scoped_occurrence_ledger_le Q root (actualStreamTotal R retire initial)
    (actualStreamOwn R retire initial) (pathLimit s C)
    (fun _ z _=>actual_stream_runtime_step R retire initial valid z) term

#print axioms occurrence_size_drops
#print axioms no_occurrences_after_size
#print axioms stable_path_depth_bound_from_start
#print axioms literal_exterior_depth_one
#print axioms literal_run_value_and_cost
end J6R50Integration


