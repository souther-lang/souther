package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;

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
 * <p>Prelude helpers are keyed by their qualified name ({@code List.map}); a module's own helpers by
 * their bare name ({@code 対象明細}), and a definition another module publishes by the qualified name
 * it is reached by here. A qualified call resolves to whichever of the two declared it, a bare call
 * to the module's own — the standard library has no bare names (spec §stdlib).
 *
 * <p>{@link #own} keeps the order the module wrote its helpers in, and that is load-bearing: the
 * checks walk it and stop at the first helper they find wrong, so the order decides which one the
 * author is told about. An author reads their file from the top.
 *
 * <p>What is in the table depends on {@link InliningPolicy}, which is what an expanded tree is a
 * representation <em>of</em>. Two policies are two tables and not one table read two ways.
 */
public final class HelperTable {

    private final String module;
    private final InliningPolicy policy;
    private final Map<String, Ast.FnDef> reached;
    private final Map<String, Ast.FnDef> own;

    private HelperTable(String module, InliningPolicy policy,
                        Map<String, Ast.FnDef> reached, Map<String, Ast.FnDef> own) {
        this.module = module;
        this.policy = policy;
        this.reached = reached;
        this.own = own;
    }

    /**
     * The table a body of {@code module} is expanded against: what it declares itself, what the
     * modules it imports publish to it, and — under {@link InliningPolicy#FULL} — the standard
     * library underneath both.
     */
    public static HelperTable of(String module, Map<String, Ast.FnDef> own,
                                 Map<String, Ast.FnDef> imported, InliningPolicy policy) {
        // In the order they are written, so a module with two helpers to complain about complains
        // about the earlier one first.
        Map<String, Ast.FnDef> joined = new LinkedHashMap<>(imported);
        joined.putAll(own);
        Map<String, Ast.FnDef> reached;
        if (policy == InliningPolicy.FULL) {
            reached = new LinkedHashMap<>(Prelude.helpers());
            reached.putAll(joined);
        } else {
            reached = joined;
        }
        return new HelperTable(module, policy, reached, new LinkedHashMap<>(own));
    }

    /** The same, for a module whose own helpers are read off its declarations. */
    public static HelperTable of(Ast.Module module, Map<String, Ast.FnDef> imported,
                                 InliningPolicy policy) {
        return of(module.name(), HelperInliner.helpersOf(module), imported, policy);
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
        Map<String, Ast.FnDef> narrowed = new LinkedHashMap<>(reached);
        boolean any = false;
        for (String name : names) {
            any |= narrowed.remove(name) != null;
        }
        return any ? new HelperTable(module, policy, narrowed, own) : this;
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
    public Ast.FnDef reached(String name) {
        return reached.get(name);
    }

    /** Whether {@code name} reaches a declaration here. */
    public boolean reaches(String name) {
        return reached.containsKey(name);
    }

    /** Everything reachable, by the name it is reached by — what the call graph is built over. */
    public Map<String, Ast.FnDef> reachable() {
        return Collections.unmodifiableMap(reached);
    }

    /** The module's own helpers, in the order it wrote them. */
    public Map<String, Ast.FnDef> own() {
        return Collections.unmodifiableMap(own);
    }

    /** Whether the module declares {@code name} itself. */
    public boolean declares(String name) {
        return own.containsKey(name);
    }
}
