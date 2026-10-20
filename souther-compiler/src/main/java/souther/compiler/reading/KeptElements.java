package souther.compiler.reading;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.RecordedVisit;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.WrittenOutElements;
import souther.compiler.semantics.Accumulation;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

/**
 * The elements a call adds up or counts, read as the decisions that meet in the answer.
 *
 * <p>{@code List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [a, b])))} is made of two
 * decisions as {@code (if a.days >= 17 then a.pay else 0) + (if b.days >= 17 then b.pay else 0)}
 * is: each element is in the total or not, and the total is a function of both. So is
 * {@code List.sum(List.map(r -> if r.days >= 17 then r.pay else 0, [a, b]))}, which keeps every
 * element and decides what each is worth. What a decision is about is the application of a
 * comparison to an element, and that is all the answer is made of. The comparison stands once, in
 * the closure, and a run evaluates it once per application; the recording holds those evaluations
 * apart ({@link ControlClaim.Visit}), and {@link ElementEvaluations} is what says which evaluation
 * is which application's.
 *
 * <p>Three responsibilities, each somewhere of its own. Which elements a container holds, what
 * keeps each, what each is worth and which application made it so is {@link WrittenOutElements}'
 * answer, read of the tree the language's operations stand in; what decides a value is
 * {@link ValueChoices}'. Which evaluation is an application's is {@link ElementEvaluations}'. What a
 * run is held to is a claim about a visit to the comparison in the tree that runs, where the same
 * call stands expanded into a walk of the list. This puts them together and reads nothing of what
 * {@code filter} or {@code map} mean.
 *
 * <p><b>Read, or not joined, and never silently neither.</b> Four things are apart here, and each
 * has its own answer. That a decision exists: something keeps an element, or decides what it is
 * worth. That its decisions can be told apart: each is one comparison, applied once. That a run can
 * be held to them: the comparison is a number of the input, and a place of the tree that runs
 * records it. And that the evaluations are ones a recording keeps. A call where the first is true
 * and any later one is not is a meeting the measure did not ask about, and it is returned as that
 * with the reason, for the measure to say so. A call where the first is false — its list not
 * written in the body, nothing deciding any element — decides nothing for the answer to be a
 * function of, and is not one.
 *
 * <p>What the call consumes is the elements' values or their number. The number of a list some
 * comparison keeps is as much a function of what it kept as their total is; the number of a list
 * written out whole is not, and is no meeting. And a total of elements each of which is worth
 * what an empty total is worth does not depend on which are kept: the keeping decides nothing of
 * the answer, and is not counted as meeting.
 */
final class KeptElements {

    /** What was made of a call. */
    sealed interface Read {

        /** The decisions that meet in the answer, one factor for each: this way, and the other. */
        record Factors(List<Factor> each) implements Read { }

        /** An answer of decided elements whose decisions this could not join to evaluations. */
        record NotJoined(WhyNotJoined why) implements Read { }
    }

    private final CoverageSites.Plan plan;

    /** The body where the language's operations stand, or null where there is none. */
    private final AnalysisBody analysis;

    private final Symbols symbols;

    private final DeclarationNewtypes newtypes;

    /** How names are followed to what they stand for, which is how a walk of a container reads. */
    private final ElementsWrittenOut.Reading<InputReads> names;

    KeptElements(CoverageSites.Plan plan, AnalysisBody analysis, Symbols symbols,
                 DeclarationNewtypes newtypes) {
        this.plan = plan;
        this.analysis = analysis;
        this.symbols = symbols;
        this.newtypes = newtypes;
        this.names = WrittenOutElements.reading(symbols, newtypes);
    }

    /**
     * What {@code call} is as an answer of decided elements, or null where it is not one.
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
        List<ReadMeaning.Occurrence> occurrences = each.asWritten();
        boolean valueMatters = Meetings.combinesItsElements(call);
        if (valueMatters && everyoneIsWorthWhatNothingIsWorth(call, occurrences)) {
            return null;
        }
        return switch (ElementEvaluations.of(occurrences, valueMatters,
                value -> ValueChoices.of(value, names))) {
            case ElementEvaluations.Result.NothingToJoin _ -> null;
            case ElementEvaluations.Result.NotJoined(var why) -> new Read.NotJoined(why);
            case ElementEvaluations.Result.Matched(var joined) -> factorsOf(call, naming, joined);
        };
    }

    /**
     * Whether every element is worth what an empty total is worth, which a total of them is
     * whichever are kept.
     */
    private boolean everyoneIsWorthWhatNothingIsWorth(Core.Call call,
                                                      List<ReadMeaning.Occurrence> occurrences) {
        Accumulation.Identity identity = Meetings.accumulationOf(call).identity();
        for (ReadMeaning.Occurrence each : occurrences) {
            if (!names.folded(new ElementsWrittenOut.Stood<>(each.value().value(),
                    each.value().at())).map(folded -> isTheIdentity(folded, identity))
                    .orElse(false)) {
                return false;
            }
        }
        return !occurrences.isEmpty();
    }

    private static boolean isTheIdentity(Object folded, Accumulation.Identity identity) {
        BigDecimal value = switch (folded) {
            case BigDecimal decimal -> decimal;
            case BigInteger whole -> new BigDecimal(whole);
            case Long whole -> BigDecimal.valueOf(whole);
            case Integer whole -> BigDecimal.valueOf(whole);
            default -> null;
        };
        if (value == null) {
            return false;
        }
        return switch (identity) {
            case ZERO -> value.signum() == 0;
            case ONE -> value.compareTo(BigDecimal.ONE) == 0;
            case EMPTY -> false;
        };
    }

    private Read factorsOf(Core.Call call, CoverageNaming naming,
                           ElementEvaluations.Joined joined) {
        Map<Core.Binary, Core.Binary> running = new IdentityHashMap<>();
        List<Factor> factors = new ArrayList<>();
        for (ElementEvaluations.Decision decision : joined.decisions()) {
            // The evaluation is the application's place among the elements the closure was handed,
            // which a recording keeps only so far: a claim about a later one is a question nothing
            // observed can answer, so it is not made.
            if (decision.evaluation() >= RecordedVisit.MOST) {
                return new Read.NotJoined(WhyNotJoined.MORE_VISITS_THAN_ARE_RECORDED);
            }
            Core.Binary run = running.computeIfAbsent(decision.comparison(),
                    stated -> theComparisonThatRuns(call, stated));
            if (run == null) {
                return new Read.NotJoined(WhyNotJoined.NOT_ONE_COMPARISON_THAT_RUNS);
            }
            Outcome holding;
            switch (naming.sideOnVisit(decision.comparison(), run, decision.truth().at(),
                    decision.evaluation(), decision.holds())) {
                case CoverageNaming.OnVisit.Named(var outcome) -> holding = outcome;
                case CoverageNaming.OnVisit.Unnamed(var why) -> {
                    return new Read.NotJoined(why);
                }
            }
            Outcome failing;
            switch (naming.sideOnVisit(decision.comparison(), run, decision.truth().at(),
                    decision.evaluation(), !decision.holds())) {
                case CoverageNaming.OnVisit.Named(var outcome) -> failing = outcome;
                case CoverageNaming.OnVisit.Unnamed(var why) -> {
                    return new Read.NotJoined(why);
                }
            }
            factors.add(new Factor(List.of(holding, failing)));
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
