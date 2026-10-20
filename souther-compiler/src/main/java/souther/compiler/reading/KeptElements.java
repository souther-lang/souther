package souther.compiler.reading;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.WrittenOutElements;

import java.util.ArrayList;
import java.util.List;

/**
 * The elements a call adds up that a comparison keeps, read as the decisions that meet in the sum.
 *
 * <p>{@code List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [a, b])))} is made of two
 * decisions as {@code (if a.days >= 17 then a.pay else 0) + (if b.days >= 17 then b.pay else 0)}
 * is: each element is in the total or not, and the total is a function of both. What a decision is
 * about is the element, and that is all the sum is made of. The comparison stands once, in the
 * closure, and a run evaluates it once per element; the recording holds those evaluations apart
 * ({@link ControlClaim.Visit}), and {@link ElementEvaluations} is what says which evaluation is which
 * element's.
 *
 * <p>Three responsibilities, each somewhere of its own. Which elements a container holds and what
 * keeps each is {@link WrittenOutElements}' answer, read of the tree the language's operations stand
 * in. Which evaluation of the comparison is an element's is {@link ElementEvaluations}'. What a run
 * is held to is a claim about a visit to the comparison in the tree that runs, where the same call
 * stands expanded into a walk of the list. This puts them together and reads nothing of what
 * {@code filter} or {@code map} mean.
 *
 * <p>A list of more elements than a recording keeps visits of is still a meeting. It is one the
 * measure does not walk, which the group's budget says: nothing here makes it not exist.
 */
final class KeptElements {

    private final CoverageSites.Plan plan;

    /** The body where the language's operations stand, or null where there is none. */
    private final AnalysisBody analysis;

    private final Symbols symbols;

    private final DeclarationNewtypes newtypes;

    KeptElements(CoverageSites.Plan plan, AnalysisBody analysis, Symbols symbols,
                 DeclarationNewtypes newtypes) {
        this.plan = plan;
        this.analysis = analysis;
        this.symbols = symbols;
        this.newtypes = newtypes;
    }

    /**
     * What varies in {@code call}, one factor per element it adds up: the element kept, and the
     * element not. Null where {@code call} is no such call or its elements are not kept in a way
     * {@link ElementEvaluations} can join to the evaluations of one comparison.
     *
     * <p>Only a call a run makes once. The visits a recording counts are of the whole run, so a call
     * that may be made again is one whose evaluations of the comparison are not the list's.
     */
    List<Factor> factorsOf(Core.Call call, CoverageNaming naming) {
        if (analysis == null || !Meetings.combinesItsElements(call) || plan.mayRepeat(call)) {
            return null;
        }
        Core.PreservedCall written = callWritten(analysis.core(), call);
        if (written == null || !(WrittenOutElements.of(
                new Denotation(written.args().getFirst(), naming.reads()), symbols, newtypes)
                instanceof WrittenOutElements.Walked.Each each)
                || !(ElementEvaluations.of(each.asWritten())
                instanceof ElementEvaluations.Result.Matched(var joined))) {
            return null;
        }
        Core.Binary run = theComparisonThatRuns(call, joined.comparison());
        if (run == null) {
            return null;
        }
        List<Factor> factors = new ArrayList<>();
        for (int evaluation = 0; evaluation < joined.byElement().size(); evaluation++) {
            ElementEvaluations.Keeping keeping = joined.byElement().get(evaluation);
            Outcome kept = naming.sideOnVisit(joined.comparison(), run, keeping.truth().at(),
                    evaluation, keeping.holds());
            Outcome dropped = naming.sideOnVisit(joined.comparison(), run, keeping.truth().at(),
                    evaluation, !keeping.holds());
            if (kept == null || dropped == null) {
                return null;
            }
            factors.add(new Factor(List.of(kept, dropped)));
        }
        return factors;
    }

    /** The call in the tree the language's operations stand in that {@code run} is the expansion
     *  of, or null where there is none. */
    private static Core.PreservedCall callWritten(Core in, Core.Call run) {
        if (Core.withoutStanding(in) instanceof Core.PreservedCall kept
                && kept.occurrence().equals(run.occurrence())) {
            return kept;
        }
        Core.PreservedCall[] found = new Core.PreservedCall[1];
        Core.forEachChild(in, child -> {
            if (found[0] == null) {
                found[0] = callWritten(child, run);
            }
        });
        return found[0];
    }

    /** The comparison in the expansion {@code within} that is the one {@code stated} writes, or
     *  null where there is not exactly one. */
    private static Core.Binary theComparisonThatRuns(Core within, Core.Binary stated) {
        List<Core.Binary> found = new ArrayList<>();
        collect(within, stated, found);
        return found.size() == 1 ? found.getFirst() : null;
    }

    private static void collect(Core in, Core.Binary stated, List<Core.Binary> found) {
        if (Core.withoutStanding(in) instanceof Core.Binary binary
                && binary.occurrence().origin().equals(stated.occurrence().origin())) {
            found.add(binary);
        }
        Core.forEachChild(in, child -> collect(child, stated, found));
    }
}
