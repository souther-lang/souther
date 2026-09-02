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
 * <p>Total over this module's declarations, which is what makes that refusal mean something. A
 * declaration with no clauses is filed with none rather than left out, so an absent key is never a
 * declaration that had nothing to say.
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
     * @param written every declaration {@code module} makes, including the ones with no clauses
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
        if (clauses == null) {
            throw new NothingWasFiledFor(named, module);
        }
        return clauses;
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
