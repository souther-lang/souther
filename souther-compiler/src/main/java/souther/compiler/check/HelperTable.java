package souther.compiler.check;

import souther.compiler.ast.DefinitionName;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.ast.Hir;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

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
    private final Map<ReachName, HelperEntry> byReference;
    private final Map<DefinitionName, HelperEntry> byAddress;
    private final Map<DefinitionName, HelperEntry> declared;
    private final Map<DefinitionName, HelperEntry> emits;
    /** The library the table was built over — held so that a reader expanding against this table
     *  asks the same library the helpers under it came from. */
    private final Stdlib stdlib;

    private HelperTable(String module, InliningPolicy policy,
                        Map<ReachName, HelperEntry> byReference,
                        Map<DefinitionName, HelperEntry> declared,
                        Map<DefinitionName, HelperEntry> emits, Stdlib stdlib) {
        this.stdlib = stdlib;
        this.module = module;
        this.policy = policy;
        this.byReference = byReference;
        this.declared = declared;
        this.emits = emits;
        Map<DefinitionName, HelperEntry> at = new LinkedHashMap<>();
        for (HelperEntry entry : byReference.values()) {
            at.put(entry.address(), entry);
        }
        this.byAddress = Collections.unmodifiableMap(at);
    }

    /**
     * The table a body of {@code module} is expanded against, built from the three sources apart:
     * what the module declared, what it took on to emit, what the modules it imports publish to it —
     * and, under {@link InliningPolicy#FULL}, the standard library underneath all three.
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
     */
    public static HelperTable of(String module, Map<String, Hir.FnDef> declared,
                                 Map<String, Hir.FnDef> takenOn,
                                 Map<String, Hir.FnDef> imported, InliningPolicy policy,
                                 Stdlib stdlib) {
        // In the order they are written, so a module with two helpers to complain about complains
        // about the earlier one first.
        Map<DefinitionName, HelperEntry> own = new LinkedHashMap<>();
        for (Map.Entry<String, Hir.FnDef> e : declared.entrySet()) {
            HelperEntry entry = HelperEntry.own(
                    new ReachName.Bare(new ValueName.Helper(module, e.getKey())), e.getValue());
            own.put(entry.address(), entry);
        }
        Map<DefinitionName, HelperEntry> emits = new LinkedHashMap<>(own);
        for (Hir.FnDef fn : takenOn.values()) {
            HelperEntry entry = HelperEntry.reached(takenOnAs(fn), fn);
            emits.put(entry.address(), entry);
        }
        Map<ReachName, HelperEntry> reached = new LinkedHashMap<>();
        if (policy == InliningPolicy.FULL) {
            for (Map.Entry<String, Hir.FnDef> e : stdlib.helpers().entrySet()) {
                ValueName.Stdlib operation = stdlib.operation(e.getKey());
                if (operation == null) {
                    // The library keys its helpers and its operations by one qualified name, so a
                    // helper with no operation is a library that disagrees with itself about what
                    // it publishes — and what would be built here is a reach name spelled out of
                    // the key, which is the join this table exists to have no way of making.
                    throw new IllegalStateException("the library holds a helper `" + e.getKey()
                            + "` and says nothing about what name reaches it");
                }
                HelperEntry entry = HelperEntry.reached(new ReachName.OfLibrary(operation),
                        e.getValue());
                reached.put(entry.reachedAs(), entry);
            }
        }
        for (Hir.FnDef fn : imported.values()) {
            HelperEntry entry = HelperEntry.reached(takenOnAs(fn), fn);
            reached.put(entry.reachedAs(), entry);
        }
        for (HelperEntry entry : emits.values()) {
            reached.put(entry.reachedAs(), entry);
        }
        return new HelperTable(module, policy, Collections.unmodifiableMap(reached),
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
    private static ReachName takenOnAs(Hir.FnDef fn) {
        ReachName reference = fn.takenOnAs();
        if (reference == null) {
            throw new IllegalStateException("`" + fn.name() + "` was handed to " + fn.declaredIn()
                    + "'s reader without saying how that reader reaches it");
        }
        return reference;
    }

    /** The same, reading the two components off the module rather than being handed them. */
    public static HelperTable of(Hir.Module module, Map<String, Hir.FnDef> imported,
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
     */
    public HelperTable hiding(Collection<ReachName> references) {
        Map<ReachName, HelperEntry> narrowed = new LinkedHashMap<>(byReference);
        boolean any = false;
        for (ReachName reference : references) {
            any |= narrowed.remove(reference) != null;
        }
        return any ? new HelperTable(module, policy, Collections.unmodifiableMap(narrowed),
                declared, emits, stdlib) : this;
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
    public Hir.FnDef reached(ReachName reference) {
        HelperEntry entry = byReference.get(reference);
        return entry == null ? null : entry.definition();
    }

    /** Whether {@code reference} reaches a declaration here. */
    public boolean reaches(ReachName reference) {
        return byReference.containsKey(reference);
    }

    /** Everything reachable, by the reference it is reached by — what the call graph is built
     * over. */
    public Map<ReachName, HelperEntry> reachable() {
        return byReference;
    }

    /**
     * What this module holds at {@code address}, or null where it holds nothing there.
     *
     * <p>An address lookup and not a resolution. What comes back is the entry that was filed there,
     * so a caller wanting the reference reads it off the entry rather than working one out of the
     * address — which for a library operation cannot be done at all.
     */
    public HelperEntry at(DefinitionName address) {
        return byAddress.get(address);
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
     * the same policy.
     *
     * <p>Said outright because a query answer is compared this way: an answer that differed between
     * two readings of one source would make every edit look like a change to everything downstream.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof HelperTable t
                && module.equals(t.module) && policy == t.policy
                && byReference.equals(t.byReference) && byAddress.equals(t.byAddress)
                && declared.equals(t.declared)
                && emits.equals(t.emits) && stdlib.equals(t.stdlib);
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(module, policy, byReference, byAddress, declared, emits,
                stdlib);
    }

    @Override
    public String toString() {
        return "HelperTable[" + module + ", " + policy + ", " + byReference.size()
                + " reachable]";
    }
}
