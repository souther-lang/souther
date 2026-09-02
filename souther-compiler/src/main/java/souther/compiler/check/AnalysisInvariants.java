package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.TheCompilerDisagreesWithItself;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * The clauses of a module's declarations in the representation a static analysis reads — the
 * language's own operations left standing ({@link InliningPolicy#DISCHARGE}).
 *
 * <p>A value and not a map, because the question a reader asks has three answers and a map has two.
 * A declaration this module wrote has a form here; one another module wrote never does, and reads as
 * the settled clauses that travel with it; and a declaration this module wrote with nothing filed
 * for it is this compiler having failed to hand its own reading over. In a map the last two are one
 * absent key, so a reader falling back to the settled form for the second falls back to it for the
 * third and says nothing while it does.
 *
 * <p>So the two are told apart by where the declaration was written and not by whether a lookup
 * found something. {@link #clausesOf} answers the settled clauses for another module's declaration
 * because that is what its analysis representation <em>is</em> (spec §invariant-discharge), and
 * refuses to answer for one of this module's that is missing.
 *
 * <p>What is filed is the declarations that wrote a clause. Whether an absent one is a gap is asked
 * of the declaration — it wrote clauses or it did not — rather than by holding a key for every
 * declaration a module makes. Held the other way this value would change when a declaration with no
 * clause was written, and everything a module's clauses are read by would be worked out again for a
 * declaration that cannot change any of it.
 *
 * <p>Refused as a disagreement and not as a limit. An analysis that meets a shape it has no rule for
 * falls open and the run-time check stands; this is the other kind, and swallowing it would leave a
 * declaration read in the wrong representation looking exactly like one read in the right one and
 * found to state little.
 */
public final class AnalysisInvariants {

    private final String module;
    private final Map<TypeSymbol.AtModule, List<Hir.InvariantClause>> written;

    /**
     * What {@code module} wrote, keyed by the declaration that wrote it.
     *
     * @param written the declarations of {@code module} that wrote a clause, and only those — a
     *        declaration with none is left out and is read as having none, not as one this is
     *        missing
     */
    public AnalysisInvariants(String module,
                              Map<TypeSymbol.AtModule, List<Hir.InvariantClause>> written) {
        if (module == null) {
            throw new IllegalArgumentException("an analysis representation is some module's");
        }
        Map<TypeSymbol.AtModule, List<Hir.InvariantClause>> copy = new LinkedHashMap<>();
        written.forEach((named, clauses) -> {
            if (!module.equals(named.module())) {
                throw new IllegalArgumentException(
                        named + " is not declared by " + module);
            }
            copy.put(named, List.copyOf(clauses));
        });
        this.module = module;
        this.written = Map.copyOf(copy);
    }

    /** The module whose declarations this holds the analysis representation of. */
    public String module() {
        return module;
    }

    /**
     * Two of these are one where they are the same clauses of the same module.
     *
     * <p>An answer of a query, so what it is settled by decides what a reader downstream is asked
     * to do again: read as one thing, a module whose clauses are what they were leaves everything
     * that reads them where it was, and read as two, a blank line anywhere re-checks every body.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof AnalysisInvariants each
                && module.equals(each.module) && written.equals(each.written);
    }

    @Override
    public int hashCode() {
        return module.hashCode() * 31 + written.hashCode();
    }

    /**
     * The clauses of {@code named} as the analysis reads them, with {@code data} the declaration
     * they were written on.
     *
     * <p>A declaration another module made is read in the form that travels with it, which is the
     * settled one: its operations have already become the folds they are derived from, and that is
     * where an imported clause falls outside the statically dischargeable fragment
     * (spec §invariant-discharge). Not a fallback — it is what that declaration's analysis
     * representation is, and there is no other.
     */
    public List<Hir.InvariantClause> clausesOf(TypeSymbol.AtModule named, Hir.Data data) {
        if (named == null || !module.equals(named.module())) {
            return data.invariants();
        }
        List<Hir.InvariantClause> clauses = written.get(named);
        if (clauses != null) {
            return clauses;
        }
        // Nothing filed, which the declaration itself tells apart: one that wrote no clause has
        // none to read, and one that wrote clauses and has none here is this module's reading
        // having failed to arrive. Asked of the declaration and not of a key for every one of them,
        // so that writing a declaration with no clause leaves this value where it was.
        if (!data.invariants().isEmpty()) {
            throw new NothingWasFiledFor(named, module);
        }
        return List.of();
    }

    /**
     * Raised where a declaration of this module has no analysis representation filed for it.
     *
     * <p>Not an ordinary limit, and said so by the interface it carries: the reading below falls
     * open on anything it has no rule for, and this failure has to cross that, or a declaration
     * whose reading was never handed over is reported as one that was read and stated little.
     */
    public static final class NothingWasFiledFor extends RuntimeException
            implements TheCompilerDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        NothingWasFiledFor(TypeSymbol.AtModule named, String module) {
            super("no analysis representation was filed for " + named + ", which " + module
                    + " declares");
        }
    }
}
