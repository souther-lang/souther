package souther.compiler.check;

import souther.compiler.stdlib.Stdlib;
import souther.compiler.ast.Hir;

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
 * <p>The library's helpers are keyed by their qualified name ({@code List.map}); a module's own helpers by
 * their bare name ({@code 対象明細}), and a definition another module publishes by the qualified name
 * it is reached by here. A qualified call resolves to whichever of the two declared it, a bare call
 * to the module's own — the standard library has no bare names (spec §stdlib).
 *
 * <p>Three questions are asked of what is here, and each has a surface of its own, so a caller
 * cannot ask one and be answered by another:
 *
 * <ul>
 *   <li>{@link #reached} — which declaration a call expands to. A call edge, asked with a reach name.
 *   <li>{@link #declarations} — what this module's source wrote. Declarations, keyed by the names it
 *       declared them under.
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
 * ({@link Hir.FnDef#declaredBy}), because the name it is reached by cannot — {@code List.foldFrom}
 * is reached under the library's alias and declared in {@code souther.list}.
 *
 * <p>What is in the table depends on {@link InliningPolicy}, which is what an expanded tree is a
 * representation <em>of</em>. Two policies are two tables and not one table read two ways.
 */
public final class HelperTable {

    private final String module;
    private final InliningPolicy policy;
    private final Map<String, Hir.FnDef> reached;
    private final Map<String, Hir.FnDef> declared;
    private final Map<String, Hir.FnDef> emits;
    /** The library the table was built over — held so that a reader expanding against this table
     *  asks the same library the helpers under it came from. */
    private final Stdlib stdlib;

    private HelperTable(String module, InliningPolicy policy, Map<String, Hir.FnDef> reached,
                        Map<String, Hir.FnDef> declared, Map<String, Hir.FnDef> emits,
                        Stdlib stdlib) {
        this.stdlib = stdlib;
        this.module = module;
        this.policy = policy;
        this.reached = reached;
        this.declared = declared;
        this.emits = emits;
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
     */
    public static HelperTable of(String module, Map<String, Hir.FnDef> declared,
                                 Map<String, Hir.FnDef> takenOn,
                                 Map<String, Hir.FnDef> imported, InliningPolicy policy,
                                 Stdlib stdlib) {
        // In the order they are written, so a module with two helpers to complain about complains
        // about the earlier one first.
        Map<String, Hir.FnDef> emits = new LinkedHashMap<>(declared);
        emits.putAll(takenOn);
        Map<String, Hir.FnDef> joined = new LinkedHashMap<>(imported);
        joined.putAll(emits);
        Map<String, Hir.FnDef> reached;
        if (policy == InliningPolicy.FULL) {
            reached = new LinkedHashMap<>(stdlib.helpers());
            reached.putAll(joined);
        } else {
            reached = joined;
        }
        return new HelperTable(module, policy, reached, new LinkedHashMap<>(declared), emits,
                stdlib);
    }

    /** The same, reading the two components off the module rather than being handed them. */
    public static HelperTable of(Hir.Module module, Map<String, Hir.FnDef> imported,
                                 InliningPolicy policy, Stdlib stdlib) {
        return of(module.name(), HelperInliner.helpersOf(module),
                HelperInliner.takenOnBy(module), imported, policy, stdlib);
    }

    /**
     * The same table with {@code names} unreachable.
     *
     * <p>What a body of a recursive helper reaches is narrowed by its own parameters: a parameter
     * sharing a helper's name — {@code foldFrom}'s function parameter {@code step} in a module that
     * also declares a helper {@code step} — is a parameter application and not a call to that helper.
     *
     * <p>This narrows what a call expands to. It does not change what recurses: the call graph is a
     * fact about the declarations, worked out over the table as it was built, and a graph taken over
     * a narrowed table would find {@code foldFrom} non-recursive and expand its self-call forever.
     */
    public HelperTable hiding(Collection<String> names) {
        Map<String, Hir.FnDef> narrowed = new LinkedHashMap<>(reached);
        boolean any = false;
        for (String name : names) {
            any |= narrowed.remove(name) != null;
        }
        return any ? new HelperTable(module, policy, narrowed, declared, emits, stdlib) : this;
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

    /** The declaration {@code name} reaches, or null where it reaches none. */
    public Hir.FnDef reached(String name) {
        return reached.get(name);
    }

    /** Whether {@code name} reaches a declaration here. */
    public boolean reaches(String name) {
        return reached.containsKey(name);
    }

    /** Everything reachable, by the name it is reached by — what the call graph is built over. */
    public Map<String, Hir.FnDef> reachable() {
        return Collections.unmodifiableMap(reached);
    }

    /** What this module's source wrote, in the order it wrote it. A helper the module only took on to
     * emit is not among these, however it is reached — and which of the two one is, the declaration
     * says ({@link Hir.FnDef#declaredBy}); a rule about the declaring module asks it there rather
     * than reading which component a fn arrived in. */
    public Map<String, Hir.FnDef> declarations() {
        return Collections.unmodifiableMap(declared);
    }

    /** What this module has as fns of its own, in the order it wrote its own: what it declared, and
     * what it took on to emit. Not what becomes a method — that is decided at lowering. Which of the
     * two one is, the declaration says ({@link Hir.FnDef#declaredBy}). */
    public Map<String, Hir.FnDef> held() {
        return Collections.unmodifiableMap(emits);
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
                && reached.equals(t.reached) && declared.equals(t.declared)
                && emits.equals(t.emits) && stdlib.equals(t.stdlib);
    }

    @Override
    public int hashCode() {
        return java.util.Objects.hash(module, policy, reached, declared, emits, stdlib);
    }

    @Override
    public String toString() {
        return "HelperTable[" + module + ", " + policy + ", " + reached.size() + " reachable]";
    }
}
