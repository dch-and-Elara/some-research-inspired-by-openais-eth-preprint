import J6R52CacheSourceWords

/-! The second actual raw framer consumer is the R48 adjacent
port writer, not just the selected seat/roster replay. It consumes
the same retained list, writes actual raw ports and preserves the
existing exact route and its original copy fee. -/
namespace J6R52CacheSource
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10
open J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R41StructuredAllPaths
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R50SourceProducer J6R32ChildResidentTransfer
open J6R33GeneratedChildSite J6R48RawRoute J6R51ParentFrames J6R51Online
open J6R34RootAtlas J6R10Repack J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 10500000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)

def cachedEmitNext {a k : ℕ} (S : SiteInputs Q previous)
    (cache : CachedParentFrames S) (L : NextSeats (childOrder S) a k) :
    Meter (Option (List (PortRow (Q.port+1)))) :=
  let copy := writeNextRows cache.rows L.rows
  ⟨copy.result,copy.steps+2⟩

theorem cached_emit_next_exact {a k : ℕ} (S : SiteInputs Q previous)
    (cache : CachedParentFrames S) (L : NextSeats (childOrder S) a k) :
    cachedEmitNext S cache L=emitNext S L := by
  unfold cachedEmitNext emitNext
  rw [cache.exactRows]

/-- Build the typed physical object directly, without invoking the
old physical writer just to update one of its fields. -/
def fromPortEmission {a k : ℕ} (S : SiteInputs Q previous)
    (d : J6R12Blueprint.Ready SP (sourceDelta s) v.child) (t : Center SP v.child)
    (L : NextSeats (childOrder S) a k)
    (groups : ∀ p : Port v.child.host.Edge,(groupOf L.seat p).val=(physicalGroup sel d t p).val)
    (write : Meter (Option (List (PortRow (Q.port+1)))))
    (has : write.result=some ((pairedPorts (childOrder S)).map (nextRecord S L.seat))) :
    Meter (PhysicalPorts sel d t (Q.port+1)) :=
  ⟨{raw := write.result.getD []
    order := pairedPorts (childOrder S)
    nodup := paired_ports_nodup _ (child_order_complete S).1
    complete := fun p=>(mem_paired_ports p _).mpr ((child_order_complete S).2 (edge p))
    record := nextRecord S L.seat
    source := by rw [has]; rfl
    labelled := groups
    distinct := next_record_key_inj S L.seat},
   write.steps⟩

theorem from_port_emission_exact {a k : ℕ} (S : SiteInputs Q previous)
    (d : J6R12Blueprint.Ready SP (sourceDelta s) v.child) (t : Center SP v.child)
    (L : NextSeats (childOrder S) a k)
    (groups : ∀ p : Port v.child.host.Edge,(groupOf L.seat p).val=(physicalGroup sel d t p).val)
    (write : Meter (Option (List (PortRow (Q.port+1)))))
    (has : write.result=some ((pairedPorts (childOrder S)).map (nextRecord S L.seat)))
    (same : write=emitNext S L) :
    fromPortEmission S d t L groups write has=⟨emittedPhysical S d t L groups,(emitNext S L).steps⟩ := by
  subst write
  rfl

def cachedPhysicalPorts {a k : ℕ} (S : SiteInputs Q previous)
    (d : J6R12Blueprint.Ready SP (sourceDelta s) v.child) (t : Center SP v.child)
    (L : NextSeats (childOrder S) a k)
    (groups : ∀ p : Port v.child.host.Edge,(groupOf L.seat p).val=(physicalGroup sel d t p).val)
    (cache : CachedParentFrames S) : Meter (PhysicalPorts sel d t (Q.port+1)) :=
  fromPortEmission S d t L groups (cachedEmitNext S cache L)
    ((congrArg Meter.result (cached_emit_next_exact S cache L)).trans (emit_next_exact S L).1)

theorem cached_physical_ports_are_real {a k : ℕ} (S : SiteInputs Q previous)
    (d : J6R12Blueprint.Ready SP (sourceDelta s) v.child) (t : Center SP v.child)
    (L : NextSeats (childOrder S) a k)
    (groups : ∀ p : Port v.child.host.Edge,(groupOf L.seat p).val=(physicalGroup sel d t p).val)
    (cache : CachedParentFrames S) :
    (cachedPhysicalPorts S d t L groups cache).result.raw=(cachedEmitNext S cache L).result.getD [] := rfl

theorem cached_physical_ports_exact {a k : ℕ} (S : SiteInputs Q previous)
    (d : J6R12Blueprint.Ready SP (sourceDelta s) v.child) (t : Center SP v.child)
    (L : NextSeats (childOrder S) a k)
    (groups : ∀ p : Port v.child.host.Edge,(groupOf L.seat p).val=(physicalGroup sel d t p).val)
    (cache : CachedParentFrames S) :
    cachedPhysicalPorts S d t L groups cache=⟨emittedPhysical S d t L groups,(emitNext S L).steps⟩ :=
  from_port_emission_exact S d t L groups _ _ (cached_emit_next_exact S cache L)

def cachedAdjacent {w : (@Plan f ell s sel).Slot v.child} {k : ℕ}
    (S : SiteInputs Q previous) (D : LiteralAdjacent S w k) (cache : CachedParentFrames S) :
    Meter (PhysicalFile T (successorTicket v w) (Q.port+1)) :=
  let d := ticketReady T (successorTicket v w)
  let t := (successorTicket v w).centerAt
  let L := rawLiteralNextSeats S d t D.code D.raw D.exact
  cachedPhysicalPorts S d t L (literal_next_groups S d t D.code D.raw D.exact) cache

theorem cached_adjacent_exact {w : (@Plan f ell s sel).Slot v.child} {k : ℕ}
    (S : SiteInputs Q previous) (D : LiteralAdjacent S w k) (cache : CachedParentFrames S) :
    cachedAdjacent S D cache=D.generated := by
  unfold cachedAdjacent LiteralAdjacent.generated actualNextPhysical
  dsimp only
  rw [cached_physical_ports_exact]

def substituteSeats {w : (@Plan f ell s sel).Slot v.child} {k : ℕ}
    {S : SiteInputs Q previous} (D : LiteralAdjacent S w k)
    (raw : List (SeatField A k)) (same : raw=D.raw) : LiteralAdjacent S w k :=
  {D with raw := raw, exact := same.trans D.exact}

theorem substitute_seats_exact {w : (@Plan f ell s sel).Slot v.child} {k : ℕ}
    {S : SiteInputs Q previous} (D : LiteralAdjacent S w k)
    (raw : List (SeatField A k)) (same : raw=D.raw) :
    substituteSeats D raw same=D := by
  subst raw
  cases D
  rfl

/-- Copy only the event fields and the real already measured physical
object. The legacy replayer occurs in the comparison statement only. -/
def wordsFromCachedRead (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u)
    (physical : Meter (ChildResidents A K.rankWidth))
    (same : physical.result=K.replay.resident) :
    OccurrenceWordsOnly T (successorTicket v u) key prec tw bw page :=
  let d := ticketReady T (successorTicket v u)
  let t := (successorTicket v u).centerAt
  let H : ResidentReceipt (packing sel d) (centerIndex d t)
    (registerPrecision SP v.child t) physical.result := same.symm ▸ K.replay.certificate
  have modeEq : H.modes=K.replay.certificate.modes := transported_modes K.replay.certificate same.symm
  {edge := K.event.edge
   dep := K.event.dep
   tc := K.event.tc
   tz := K.event.tz
   tm := K.event.tm
   q := K.rankWidth
   code := K.event.code
   native := K.event.native
   issued := K.event.issued
   fw := K.event.fw
   hOld := K.event.hOld
   hMod := K.event.hMod
   physical := physical
   geometry := H
   words := K.event.words
   group := K.event.group
   clock := K.event.clock
   centre := K.event.centre
   codeExact := K.event.codeExact
   codePos := K.event.codePos
   codeFit := by rw [modeEq]; exact K.event.codeFit
   acted := by rw [modeEq]; exact K.event.acted
   outerPos := K.event.outerPos
   fit := K.event.fit
   probe := K.event.probe
   width := K.event.width}

theorem words_from_cached_read_exact
    (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (physical : Meter (ChildResidents A K.rankWidth))
    (same : physical.result=K.replay.resident)
    (paid : physical=⟨K.replay.resident,(replayChild X.site u K.rankWidth K.selectedWords).steps⟩) :
    wordsFromCachedRead X u K physical same=localEventWords K.event := by
  subst physical
  rfl

/-- The one successful raw replay supplies both the measured
physical words and the concrete seats for the raw next-port writer. -/
def bindCachedReplay (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (cache : CachedParentFrames X.site)
    (physical : Meter (ChildResidents A K.rankWidth))
    (same : physical=⟨K.replay.resident,(replayChild X.site u K.rankWidth K.selectedWords).steps⟩) :
    OccurrenceInput T (successorTicket v u) key prec tw bw page :=
  let words := wordsFromCachedRead X u K physical (congrArg Meter.result same)
  let old := selectedAdjacent K.replay
  let seats := substituteSeats old physical.result.seats (congrArg (fun pay : Meter (ChildResidents A K.rankWidth)=>pay.result.seats) same)
  words.bind (cachedAdjacent X.site seats cache)

theorem bind_cached_replay_exact
    (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (cache : CachedParentFrames X.site)
    (physical : Meter (ChildResidents A K.rankWidth))
    (same : physical=⟨K.replay.resident,(replayChild X.site u K.rankWidth K.selectedWords).steps⟩) :
    bindCachedReplay X u K cache physical same=localEventInput K.event := by
  unfold bindCachedReplay localEventInput
  dsimp only
  rw [cached_adjacent_exact,substitute_seats_exact,words_from_cached_read_exact X u K physical _ same]

def cachedRoutedInput (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (cache : CachedParentFrames X.site) :
    OccurrenceInput T (successorTicket v u) key prec tw bw page :=
  bindCachedReplay X u K cache (cachePhysical X.site u K.rankWidth K.selectedWords cache K.replay)
    (cache_physical_exact X.site u K.rankWidth K.selectedWords cache K.replay)

theorem cached_routed_input_exact
    (X : StoredSite T v key prec tw bw page) (u : (@Plan f ell s sel).Slot v.child)
    (K : LocalLoad X u) (cache : CachedParentFrames X.site) :
    cachedRoutedInput X u K cache=localEventInput K.event :=
  bind_cached_replay_exact X u K cache _ (cache_physical_exact X.site u K.rankWidth K.selectedWords cache K.replay)

#print axioms cached_emit_next_exact
#print axioms cached_physical_ports_are_real
#print axioms cached_physical_ports_exact
#print axioms cached_adjacent_exact
#print axioms words_from_cached_read_exact
#print axioms bind_cached_replay_exact
#print axioms cached_routed_input_exact
end
end J6R52CacheSource
