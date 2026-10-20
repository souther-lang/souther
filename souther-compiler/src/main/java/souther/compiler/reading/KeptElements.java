package souther.compiler.reading;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.check.ScopeStep;
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
import java.util.OptionalInt;
import java.util.function.Predicate;

/**
 * The elements a call adds up or counts, read as the decisions that meet in the answer.
 *
 * <p>{@code List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [a, b])))} is made of two
 * decisions as {@code (if a.days >= 17 then a.pay else 0) + (if b.days >= 17 then b.pay else 0)}
 * is: each element is in the total or not, and the total is a function of both. So is
 * {@code List.sum(List.map(r -> if r.days >= 17 then r.pay else 0, [a, b]))}, which keeps every
 * element and decides what each is worth, and so is the same list written with the choices in it.
 * What a decision is about is the application of a comparison to an element, and that is all the
 * answer is made of. A comparison in a closure is evaluated once per application and the recording
 * holds those evaluations apart ({@link ControlClaim.Visit}); one a run evaluates once needs no
 * number. {@link ElementEvaluations} is what says which evaluation is which application's.
 *
 * <p>Three responsibilities, each somewhere of its own. Which elements a container holds, what
 * keeps each, what each is worth and which application made it so is {@link WrittenOutElements}'
 * answer; what decides a value is {@link ValueChoices}'. Which evaluation is an application's is
 * {@link ElementEvaluations}'. What a run is held to is a claim about a visit to the comparison in
 * the tree that runs, where the same call stands expanded into a walk of the list, and whether the
 * comparison is visited more than once is a fact of that tree. This puts them together and reads
 * nothing of what {@code filter} or {@code map} mean.
 *
 * <p>Read in the tree the language's operations stand in, with the names that tree binds. It and
 * the tree that runs are two expansions of one body, each with the bindings of its own, so a list
 * named by a {@code let} is a name in the first and a name the second's reading has never seen.
 * The call is found by walking the first the way it is read, entering each scope on the way.
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
 * written out whole is not, and is no meeting. And an element worth what an empty total is worth
 * does not change a total, kept or not: what keeps it, and what decides it, are no decision of the
 * answer.
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

    /** What the names of that body are read in at its root, or null where there is no body. */
    private final InputReads analysisReads;

    private final Symbols symbols;

    private final DeclarationNewtypes newtypes;

    /** How names are followed to what they stand for, which is how a walk of a container reads. */
    private final ElementsWrittenOut.Reading<InputReads> names;

    KeptElements(CoverageSites.Plan plan, AnalysisBody analysis, InputReads analysisReads,
                 Symbols symbols, DeclarationNewtypes newtypes) {
        this.plan = plan;
        this.analysis = analysis;
        this.analysisReads = analysisReads;
        this.symbols = symbols;
        this.newtypes = newtypes;
        this.names = WrittenOutElements.reading(symbols, newtypes);
    }

    /** A call of the tree the language's operations stand in, and the reading its names are read
     *  in where it stands. */
    private record Written(Core.PreservedCall call, InputReads at) { }

    /**
     * What {@code call} is as an answer of decided elements, or null where it is not one.
     *
     * <p>Only a call a run makes once. The visits a recording counts are of the whole run, so a call
     * that may be made again is one whose evaluations of the comparison are not the list's.
     *
     * @param body the body {@code call} is in, in the tree that runs
     * @param compared whether {@code call} is an operand of a comparison
     */
    Read of(Core.Call call, CoverageNaming naming, Core body, boolean compared) {
        if (analysis == null || analysisReads == null || !Meetings.consumesItsElements(call)
                || plan.mayRepeat(call)) {
            return null;
        }
        Written written = callWritten(analysis.core(), analysisReads, call);
        if (written == null) {
            return null;
        }
        // The list as the name that holds it stands for it: a walk of a container writes out what
        // it is handed, and a name is not a list written out.
        ElementsWrittenOut.Stood<InputReads> container =
                names.standing(written.call().args().getFirst(), written.at());
        WrittenOutElements.Walked walked = WrittenOutElements.of(
                new Denotation(container.value(), container.at()), symbols, newtypes);
        if (walked instanceof WrittenOutElements.Walked.PastTheFigure) {
            return new Read.NotJoined(WhyNotJoined.MORE_ELEMENTS_THAN_ARE_WRITTEN_OUT);
        }
        if (!(walked instanceof WrittenOutElements.Walked.Each each)) {
            return null;
        }
        boolean valueMatters = Meetings.combinesItsElements(call);
        return switch (ElementEvaluations.of(each.asWritten(), contributing(call, valueMatters),
                valueMatters, !valueMatters && compared,
                value -> ValueChoices.of(value, names, newtypes))) {
            case ElementEvaluations.Result.NothingToJoin _ -> null;
            case ElementEvaluations.Result.NotJoined(var why) -> new Read.NotJoined(why);
            case ElementEvaluations.Result.Matched(var joined) ->
                    factorsOf(call, naming, body, joined);
        };
    }

    /**
     * Whether an occurrence can change what {@code call} answers: always for a count, and for a
     * total unless the occurrence is worth what an empty total is worth.
     */
    private Predicate<ReadMeaning.Occurrence> contributing(Core.Call call, boolean valueMatters) {
        if (!valueMatters) {
            return _ -> true;
        }
        Accumulation.Identity identity = Meetings.accumulationOf(call).identity();
        return occurrence -> !names.folded(new ElementsWrittenOut.Stood<>(
                        occurrence.value().value(), occurrence.value().at()))
                .map(folded -> isTheIdentity(folded, identity)).orElse(false);
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

    private Read factorsOf(Core.Call call, CoverageNaming naming, Core body,
                           ElementEvaluations.Joined joined) {
        Map<Core.Binary, Core.Binary> running = new IdentityHashMap<>();
        List<Factor> factors = new ArrayList<>();
        for (ElementEvaluations.Decision decision : joined.decisions()) {
            // In the call first, where the closure the comparison is in was expanded: there a copy
            // of a helper is told from another by being in this call. A comparison the elements
            // were written with is where they were written, which is the body and not the call.
            Core.Binary run = running.computeIfAbsent(decision.comparison(), stated -> {
                Core.Binary inTheCall = theComparisonThatRuns(call, stated);
                return inTheCall != null ? inTheCall : theComparisonThatRuns(body, stated);
            });
            if (run == null) {
                return new Read.NotJoined(WhyNotJoined.NOT_ONE_COMPARISON_THAT_RUNS);
            }
            // A comparison a run visits more than once is told apart by which visit; one it visits
            // once needs no number, whichever way its value was found. And a number the walk could
            // not give a comparison that is visited more than once is not made up.
            OptionalInt visit = OptionalInt.empty();
            if (plan.mayRepeat(run)) {
                if (decision.evaluation().isEmpty()) {
                    return new Read.NotJoined(WhyNotJoined.A_VALUE_CHOICE_NOT_NUMBERED);
                }
                // The evaluation is the application's place among the elements the closure was
                // handed, which a recording keeps only so far: a claim about a later one is a
                // question nothing observed can answer, so it is not made.
                if (decision.evaluation().getAsInt() >= RecordedVisit.MOST) {
                    return new Read.NotJoined(WhyNotJoined.MORE_VISITS_THAN_ARE_RECORDED);
                }
                visit = decision.evaluation();
            }
            Outcome holding;
            switch (naming.sideOnVisit(decision.comparison(), run, decision.truth().at(), visit,
                    decision.holds())) {
                case CoverageNaming.OnVisit.Named(var outcome) -> holding = outcome;
                case CoverageNaming.OnVisit.Unnamed(var why) -> {
                    return new Read.NotJoined(why);
                }
            }
            Outcome failing;
            switch (naming.sideOnVisit(decision.comparison(), run, decision.truth().at(), visit,
                    !decision.holds())) {
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
     *  of, with the reading of its names where it stands, or null where there is none. */
    private Written callWritten(Core in, InputReads at, Core.Call run) {
        if (Core.withoutStanding(in) instanceof Core.PreservedCall kept
                && kept.occurrence().equals(run.occurrence())) {
            return new Written(kept, at);
        }
        Written[] found = new Written[1];
        ScopeStep.forEachChild(in, (child, step) -> {
            if (found[0] == null) {
                found[0] = callWritten(child, at.entering(step, symbols, newtypes), run);
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
