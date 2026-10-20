package souther.compiler.reading;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.RecordedVisit;
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
 * about is the application of the comparison to an element, and that is all the sum is made of. The
 * comparison stands once, in the closure, and a run evaluates it once per application; the
 * recording holds those evaluations apart ({@link ControlClaim.Visit}), and
 * {@link ElementEvaluations} is what says which evaluation is which application's.
 *
 * <p>Three responsibilities, each somewhere of its own. Which elements a container holds, what
 * keeps each and which application kept it is {@link WrittenOutElements}' answer, read of the tree
 * the language's operations stand in. Which evaluation is an application's is
 * {@link ElementEvaluations}'. What a run is held to is a claim about a visit to the comparison in
 * the tree that runs, where the same call stands expanded into a walk of the list. This puts them
 * together and reads nothing of what {@code filter} or {@code map} mean.
 *
 * <p><b>Read, or not joined, and never silently neither.</b> Four things are apart here, and each
 * has its own answer. That a decision exists: something keeps an element. That its decisions can be
 * told apart: each element is kept by one comparison, applied once. That a run can be held to them:
 * the comparison is a number of the input, and a place of the tree that runs records it. And that
 * the evaluations are ones a recording keeps. A call where the first is true and any later one is
 * not is a meeting the measure did not ask about, and it is returned as that with the reason, for
 * the measure to say so. A call where the first is false — its list not written in the body, no
 * element kept by anything — decides nothing for the sum to be a function of, and is not one.
 *
 * <p>What the sum consumes is the elements' values or their number. The number of a list some
 * comparison keeps is as much a function of what it kept as their total is; the number of a list
 * written out whole is not, and is no meeting.
 */
final class KeptElements {

    /** What was made of a call. */
    sealed interface Read {

        /** The decisions that meet in the sum, one factor for each application: kept, and not. */
        record Factors(List<Factor> each) implements Read { }

        /** A sum of kept elements whose decisions this could not join to evaluations. */
        record NotJoined(WhyNotJoined why) implements Read { }
    }

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
     * What {@code call} is as a sum of kept elements, or null where it is not one.
     *
     * <p>Only a call a run makes once. The visits a recording counts are of the whole run, so a call
     * that may be made again is one whose evaluations of the comparison are not the list's.
     */
    Read of(Core.Call call, CoverageNaming naming) {
        if (analysis == null || !Meetings.consumesItsElements(call) || plan.mayRepeat(call)) {
            return null;
        }
        Core.PreservedCall written = callWritten(analysis.core(), call);
        if (written == null) {
            return null;
        }
        WrittenOutElements.Walked walked = WrittenOutElements.of(
                new Denotation(written.args().getFirst(), naming.reads()), symbols, newtypes);
        if (walked instanceof WrittenOutElements.Walked.PastTheFigure) {
            return new Read.NotJoined(WhyNotJoined.MORE_ELEMENTS_THAN_ARE_WRITTEN_OUT);
        }
        if (!(walked instanceof WrittenOutElements.Walked.Each each)) {
            return null;
        }
        return switch (ElementEvaluations.of(each.asWritten())) {
            case ElementEvaluations.Result.NothingToJoin _ -> null;
            case ElementEvaluations.Result.NotJoined(var why) -> new Read.NotJoined(why);
            case ElementEvaluations.Result.Matched(var joined) -> factorsOf(call, naming, joined);
        };
    }

    private Read factorsOf(Core.Call call, CoverageNaming naming,
                           ElementEvaluations.Joined joined) {
        Core.Binary run = theComparisonThatRuns(call, joined.comparison());
        if (run == null) {
            return new Read.NotJoined(WhyNotJoined.NOT_ONE_COMPARISON_THAT_RUNS);
        }
        List<Factor> factors = new ArrayList<>();
        for (ElementEvaluations.Keeping keeping : joined.byEvaluation()) {
            // The evaluation is the application's place among the elements the closure was handed,
            // which a recording keeps only so far: a claim about a later one is a question nothing
            // observed can answer, so it is not made.
            if (keeping.evaluation() >= RecordedVisit.MOST) {
                return new Read.NotJoined(WhyNotJoined.MORE_VISITS_THAN_ARE_RECORDED);
            }
            Outcome kept;
            switch (naming.sideOnVisit(joined.comparison(), run, keeping.truth().at(),
                    keeping.evaluation(), keeping.holds())) {
                case CoverageNaming.OnVisit.Named(var outcome) -> kept = outcome;
                case CoverageNaming.OnVisit.Unnamed(var why) -> {
                    return new Read.NotJoined(why);
                }
            }
            Outcome dropped;
            switch (naming.sideOnVisit(joined.comparison(), run, keeping.truth().at(),
                    keeping.evaluation(), !keeping.holds())) {
                case CoverageNaming.OnVisit.Named(var outcome) -> dropped = outcome;
                case CoverageNaming.OnVisit.Unnamed(var why) -> {
                    return new Read.NotJoined(why);
                }
            }
            factors.add(new Factor(List.of(kept, dropped)));
        }
        return new Read.Factors(factors);
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
