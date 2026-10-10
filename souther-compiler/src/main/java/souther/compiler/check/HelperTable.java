package souther.compiler.check;

import souther.compiler.ast.DefinitionName;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.ast.Hir;
import souther.compiler.identity.DecidedByTheRest;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;

/**
 * Which declaration a name reaches where a body of one module is expanded.
 *
 * <p>A value, and the same value for every body of that module: which helper a call expands to
 * follows from the declarations around it and from nothing about the call. Held as a value rather
 * than built per expansion, so the eleven questions that expand something in a compile are reading
 * one answer rather than eleven that have to agree.
 *
 * <p>Everything here is a {@link HelperEntry}, and the maps are indexes of the same entries. An
 * entry pairs the reference a call reaches a declaration by with the address this module holds it
 * at, and that pairing is made once — where the entry is built out of what the declaration says and
 * what module is reading. Two maps holding the two coordinates apart would be two statements of one
 * correspondence, and a reader that had an address and wanted the reference would spell it back out.
 *
 * <p>The library's helpers are reached under the alias the library publishes them by
 * ({@code List.map}); a module's own by their bare name ({@code 対象明細}), and a definition another
 * module publishes under the module that declares it. A qualified call reaches whichever of the two
 * declared it, a bare call the module's own — the standard library has no bare names (spec
 * §stdlib).
 *
 * <p>Three questions are asked of what is here, and each has a surface of its own, so a caller
 * cannot ask one and be answered by another:
 *
 * <ul>
 *   <li>{@link #reached} — which declaration a call expands to. A call edge, asked with the
 *       reference resolution settled, never with a spelling.
 *   <li>{@link #declarations} — what this module's source wrote, at the addresses it wrote them.
 *   <li>{@link #held} — what this module has as fns of its own: what it declared, and what it took
 *       on to emit for lack of anywhere else to put it.
 * </ul>
 *
 * <p>{@link #held} is not what becomes a method. Most of what a module declares is expanded into its
 * callers and emitted nowhere, and a value has no method form at all; which of these survive is
 * decided at lowering, over this and the answers about recursion and rows. What is held here is the
 * question of whose fn it is, which is the one every check needs.
 *
 * <p>{@link #held} keeps the order the module wrote its helpers in, and that is load-bearing: the
 * checks walk it and stop at the first helper they find wrong, so the order decides which one the
 * author is told about. An author reads their file from the top.
 *
 * <p>Nothing here answers which module declared a taken-on helper: the declaration answers that
 * ({@link Hir.FnDef#declaredBy}), because the reference it is reached by cannot —
 * {@code List.foldFrom} is reached under the library's alias and declared in {@code souther.list}.
 *
 * <p>What is in the table depends on {@link InliningPolicy}, which is what an expanded tree is a
 * representation <em>of</em>. Two policies are two tables and not one table read two ways.
 */
public final class HelperTable {

    private final String module;
    private final InliningPolicy policy;
    private final SequencedMap<ReachName.Declaration, HelperEntry> byReference;
    private final Map<DefinitionName, HelperEntry> byAddress;
    private final Map<DefinitionName, HelperEntry> declared;
    private final Map<DefinitionName, HelperEntry> emits;
    /** How each entry of {@code emits} is reached — read off the entries, as {@code byAddress} is. */
    @DecidedByTheRest
    private final Set<ReachName.Declaration> heldAs;
    /** What {@link #hiding} made unreachable: references {@code byReference} holds and a call here
     *  does not reach. Empty for a table as it was built. */
    private final Set<ReachName.Declaration> hidden;
    /** {@code byReference} less {@code hidden}, made the first time {@link #reachable} is asked of a
     *  table that hides something. */
    private volatile SequencedMap<ReachName.Declaration, HelperEntry> narrowed;
    /** The library the table was built over — held so that a reader expanding against this table
     *  asks the same library the helpers under it came from. */
    private final Stdlib stdlib;

    private HelperTable(String module, InliningPolicy policy,
                        SequencedMap<ReachName.Declaration, HelperEntry> byReference,
                        Map<DefinitionName, HelperEntry> byAddress,
                        Map<DefinitionName, HelperEntry> declared,
                        Map<DefinitionName, HelperEntry> emits,
                        Set<ReachName.Declaration> heldAs,
                        Set<ReachName.Declaration> hidden, Stdlib stdlib) {
        this.stdlib = stdlib;
        this.module = module;
        this.policy = policy;
        this.byReference = byReference;
        this.byAddress = byAddress;
        this.declared = declared;
        this.emits = emits;
        this.heldAs = heldAs;
        this.hidden = hidden;
    }

    /** A table hiding nothing, with its indexes read off {@code byReference} and {@code emits}. */
    private static HelperTable built(String module, InliningPolicy policy,
                                     SequencedMap<ReachName.Declaration, HelperEntry> byReference,
                                     Map<DefinitionName, HelperEntry> declared,
                                     Map<DefinitionName, HelperEntry> emits, Stdlib stdlib) {
        Map<DefinitionName, HelperEntry> at = new LinkedHashMap<>();
        for (HelperEntry entry : byReference.values()) {
            at.put(entry.address(), entry);
        }
        Set<ReachName.Declaration> as = new HashSet<>();
        for (HelperEntry entry : emits.values()) {
            as.add(entry.reachedAs());
        }
        return new HelperTable(module, policy, byReference, Collections.unmodifiableMap(at),
                declared, emits, Collections.unmodifiableSet(as), Set.of(), stdlib);
    }

    /**
     * The table a body of {@code module} is expanded against, built from the three sources apart:
     * what the module declared, what it took on to emit, what the modules it imports publish to it —
     * and the standard library underneath all three: every helper it writes under
     * {@link InliningPolicy#FULL}, and under {@link InliningPolicy#DISCHARGE} those it is read
     * through ({@link LibraryReadThrough}).
     *
     * <p>Apart, because what a name reaches and what this module holds are two relations and one of
     * them cannot be recovered from the other. Handed a single joined map, a table answered that the
     * module has every published definition as a fn of its own, and the caller that held the three
     * apart answered that it has none of them.
     *
     * <p>Each source says how what it holds is reached, and none of them is asked to spell it. A
     * module's own is reached bare; what it took on carries the reference the expansion that took it
     * on recorded ({@link Hir.FnDef#takenOnAs}); an imported definition is reached under the module
     * that declares it, which the declaration says; a library operation is reached under the alias
     * the library publishes it by, which the library says.
     *
     * <p>{@code imported} has to have been closed under {@code policy}. Its bodies were expanded
     * where they were written, so a table of another policy would hold them in a representation
     * none of this module's own bodies is in, and nothing reading an expanded tree could tell which
     * parts were which.
     */
    public static HelperTable of(String module, Map<String, Hir.FnDef> declared,
                                 Map<String, Hir.FnDef> takenOn,
                                 ClosedImports imported, InliningPolicy policy,
                                 Stdlib stdlib) {
        if (imported.policy() != policy) {
            throw new IllegalArgumentException("a table of `" + module + "` expanding under "
                    + policy + " was handed definitions closed under " + imported.policy());
        }
        // In the order they are written, so a module with two helpers to complain about complains
        // about the earlier one first.
        Map<DefinitionName, HelperEntry> own = new LinkedHashMap<>();
        for (Map.Entry<String, Hir.FnDef> e : declared.entrySet()) {
            HelperEntry entry = HelperEntry.own(
                    new ReachName.Own(new ValueName.Helper(module, e.getKey())), e.getValue());
            own.put(entry.address(), entry);
        }
        Map<DefinitionName, HelperEntry> emits = new LinkedHashMap<>(own);
        for (Hir.FnDef fn : takenOn.values()) {
            HelperEntry entry = HelperEntry.reached(takenOnAs(fn), fn);
            emits.put(entry.address(), entry);
        }
        SequencedMap<ReachName.Declaration, HelperEntry> reached = new LinkedHashMap<>();
        Set<ValueName.Stdlib.Operation> readThrough =
                policy == InliningPolicy.FULL ? null : LibraryReadThrough.shipped();
        stdlib.helpers().forEach((operation, body) -> {
            if (readThrough == null || readThrough.contains(operation)) {
                HelperEntry entry =
                        HelperEntry.reached(new ReachName.OfLibrary(operation), body);
                reached.put(entry.reachedAs(), entry);
            }
        });
        for (Hir.FnDef fn : imported.definitions().values()) {
            HelperEntry entry = HelperEntry.reached(takenOnAs(fn), fn);
            reached.put(entry.reachedAs(), entry);
        }
        for (HelperEntry entry : emits.values()) {
            reached.put(entry.reachedAs(), entry);
        }
        return built(module, policy, Collections.unmodifiableSequencedMap(reached),
                Collections.unmodifiableMap(own), Collections.unmodifiableMap(emits), stdlib);
    }

    /**
     * The reference a definition this module did not write is reached by, off the definition.
     *
     * <p>A definition arrives here having been renamed for this module by whoever handed it over
     * ({@link Hir.FnDef#reachedAs}), and that renaming is where the reference was settled. One that
     * did not go through it has no reference for anything here to invent: reading one off the
     * declaration would answer {@code souther.list.foldFrom} for an operation reached as
     * {@code List.foldFrom}, and the definition would then answer to a name no call writes.
     */
    private static ReachName.Declaration takenOnAs(Hir.FnDef fn) {
        ReachName.Declaration reference = fn.takenOnAs();
        if (reference == null) {
            throw new IllegalStateException("`" + fn.name() + "` was handed to " + fn.declaredIn()
                    + "'s reader without saying how that reader reaches it");
        }
        return reference;
    }

    /** The same, for a module that imports nothing. */
    public static HelperTable of(String module, Map<String, Hir.FnDef> declared,
                                 Map<String, Hir.FnDef> takenOn, InliningPolicy policy,
                                 Stdlib stdlib) {
        return of(module, declared, takenOn, ClosedImports.none(policy), policy, stdlib);
    }

    /** The same, reading the two components off the module rather than being handed them. */
    public static HelperTable of(Hir.Module module, ClosedImports imported,
                                 InliningPolicy policy, Stdlib stdlib) {
        return of(module.name(), HelperInliner.helpersOf(module),
                HelperInliner.takenOnBy(module), imported, policy, stdlib);
    }

    /**
     * The same table with {@code references} unreachable.
     *
     * <p>What a body of a recursive helper reaches is narrowed by its own parameters: a parameter
     * sharing a helper's name — {@code foldFrom}'s function parameter {@code step} in a module that
     * also declares a helper {@code step} — is a parameter application and not a call to that helper.
     *
     * <p>This narrows what a call expands to. It does not change what recurses: the call graph is a
     * fact about the declarations, worked out over the table as it was built, and a graph taken over
     * a narrowed table would find {@code foldFrom} non-recursive and expand its self-call forever.
     *
     * <p>Asked for the body of every recursive helper, so nothing of the table is copied: the
     * narrowed one shares this one's maps and holds beside them the references it hides, and every
     * reader of a reference or an address asks those first. An address is read off the reference it
     * is held for, so hiding a reference hides its address with it. Only a reference this table
     * reaches is held as hidden, so hiding a name nothing reaches is this table.
     */
    public HelperTable hiding(Collection<ReachName.Declaration> references) {
        Set<ReachName.Declaration> more = null;
        for (ReachName.Declaration reference : references) {
            if (byReference.containsKey(reference) && !hidden.contains(reference)) {
                if (more == null) {
                    more = new HashSet<>(hidden);
                }
                more.add(reference);
            }
        }
        return more == null ? this : new HelperTable(module, policy, byReference, byAddress,
                declared, emits, heldAs, Collections.unmodifiableSet(more), stdlib);
    }

    /** The entry {@code reference} reaches here, or null where it reaches none or is hidden. */
    private HelperEntry entryFor(ReachName.Declaration reference) {
        return hidden.contains(reference) ? null : byReference.get(reference);
    }

    /** The library the table was built over. */
    public Stdlib library() {
        return stdlib;
    }

    /** The module whose body this expands into. */
    public String module() {
        return module;
    }

    /** What an expanded tree read against this table is a representation of. */
    public InliningPolicy policy() {
        return policy;
    }

    /** The declaration {@code reference} reaches, or null where it reaches none here. */
    public Hir.FnDef reached(ReachName.Declaration reference) {
        HelperEntry entry = entryFor(reference);
        return entry == null ? null : entry.definition();
    }

    /** Whether {@code reference} reaches a declaration here. */
    public boolean reaches(ReachName.Declaration reference) {
        return entryFor(reference) != null;
    }

    /** Everything reachable, by the reference it is reached by — what the call graph is built
     * over. In construction order and not the module's alone: the library's operations first (under
     * {@link InliningPolicy#FULL}), then the imports, then what this module declared or took on —
     * each source in the order it was handed to {@link #of}. Said in the type because a reader
     * ({@link HelperGraph}, {@code souther.compiler.query.Bodies.RequiredRecursiveDefs}) folds this
     * order into an answer whose own {@code equals} makes the order part of what it means; a map
     * that promised only membership would make that answer flap on every read of a source no edit
     * touched. */
    public SequencedMap<ReachName.Declaration, HelperEntry> reachable() {
        if (hidden.isEmpty()) {
            return byReference;
        }
        SequencedMap<ReachName.Declaration, HelperEntry> out = narrowed;
        if (out == null) {
            SequencedMap<ReachName.Declaration, HelperEntry> less = new LinkedHashMap<>(byReference);
            for (ReachName.Declaration reference : hidden) {
                less.remove(reference);
            }
            out = Collections.unmodifiableSequencedMap(less);
            narrowed = out;
        }
        return out;
    }

    /**
     * Where this module holds what {@code reference} reaches, or null where it reaches nothing
     * here.
     *
     * <p>The one place the two coordinates are put together for a caller that has one and needs the
     * other. A caller building the correspondence for itself — out of {@link #held} or
     * {@link #declarations} — would be a fourth copy of what an entry already pairs, and the day one
     * of them was built from a different reading the four would stop agreeing.
     */
    public DefinitionName heldAt(ReachName.Declaration reference) {
        HelperEntry entry = entryFor(reference);
        return entry == null ? null : entry.address();
    }

    /**
     * Whether one of the fns this module holds ({@link #held}) is the one {@code reference} reaches.
     *
     * <p>Asked of the entries, each of which already pairs the reference it is reached by with where
     * it is held. An address worked out of the reference would be a second statement of that pairing,
     * and where the two came apart a held fn would be answered as not held. Unaffected by
     * {@link #hiding}, which narrows what a call reaches and not what this module holds.
     *
     * <p>Answered from the references read off those entries when the table was made, because it
     * is asked once for every recursion in reach.
     */
    public boolean holds(ReachName.Declaration reference) {
        return heldAs.contains(reference);
    }

    /**
     * What this module holds at {@code address}, or null where it holds nothing there.
     *
     * <p>An address lookup and not a resolution. What comes back is the entry that was filed there,
     * so a caller wanting the reference reads it off the entry rather than working one out of the
     * address — which for a library operation cannot be done at all.
     */
    public HelperEntry at(DefinitionName address) {
        HelperEntry entry = byAddress.get(address);
        return entry == null || hidden.contains(entry.reachedAs()) ? null : entry;
    }

    /** What this module's source wrote, in the order it wrote it, at the addresses it wrote them.
     * A helper the module only took on to emit is not among these, however it is reached — and which
     * of the two one is, the declaration says ({@link Hir.FnDef#declaredBy}); a rule about the
     * declaring module asks it there rather than reading which component a fn arrived in. */
    public Map<DefinitionName, HelperEntry> declarations() {
        return declared;
    }

    /** What this module has as fns of its own, in the order it wrote its own: what it declared, and
     * what it took on to emit. Not what becomes a method — that is decided at lowering. Which of the
     * two one is, the declaration says ({@link Hir.FnDef#declaredBy}). */
    public Map<DefinitionName, HelperEntry> held() {
        return emits;
    }

    /**
     * Two tables are the same table when they hold the same declarations for the same module under
     * the same policy — {@code byReference} in the same order too, because {@link #reachable} makes
     * that order part of what a table means (its own Javadoc says so, and {@link HelperGraph} and
     * {@code Bodies.RequiredRecursiveDefs} fold it into answers of their own).
     * {@link Map#equals} does not see order, so it is compared as the sequence of entries it is
     * declared to be rather than handed to {@code Map.equals} directly. What a table hides is
     * compared beside them, since it changes what a call here reaches.
     *
     * <p>Said outright because a query answer is compared this way: an answer that differed between
     * two readings of one source would make every edit look like a change to everything downstream.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof HelperTable t
                && module.equals(t.module) && policy == t.policy
                && sameOrder(byReference, t.byReference) && byAddress.equals(t.byAddress)
                && declared.equals(t.declared)
                && emits.equals(t.emits) && hidden.equals(t.hidden) && stdlib.equals(t.stdlib);
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(module, policy, List.copyOf(byReference.entrySet()),
                byAddress, declared, emits, hidden, stdlib);
    }

    /** Whether {@code a} and {@code b} hold the same entries in the same order. */
    private static boolean sameOrder(SequencedMap<ReachName.Declaration, HelperEntry> a,
                                     SequencedMap<ReachName.Declaration, HelperEntry> b) {
        return List.copyOf(a.entrySet()).equals(List.copyOf(b.entrySet()));
    }

    @Override
    public String toString() {
        return "HelperTable[" + module + ", " + policy + ", "
                + (byReference.size() - hidden.size()) + " reachable]";
    }
}
