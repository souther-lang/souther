package souther.compiler.partition;

import souther.compiler.meaning.AnswerAsAnInput;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * What a composition was arrived at without, from both of the projections a way is read through.
 *
 * <p>Carried out with whatever the composition came to, and not only with the answers nothing came
 * of. A value that stands a dependency in without meeting one of the demands on it composes a row
 * as readily as one that meets them all — the row leans on what the module already states — so an
 * account kept on the failing arm alone would have nowhere to put the one case where a reader most
 * needs it, which is a row that was built and run.
 *
 * <p><b>Which conditions the answer projection took up, and not only the ones it fell short of.</b>
 * A condition about an answer is declined by the input projection whatever becomes of it, the
 * region a row is searched in being over the input's positions; so the input side's word about such
 * a condition says which projection had no use for it and says nothing about whether anything was
 * missed. Reconciling the two takes knowing which conditions the answer side answered for, and that
 * is a larger set than the ones it could not compose against.
 *
 * <p><b>And what this holds is not the whole of what a composing was arrived at without.</b> A
 * condition the walk had no words for is in neither list: nothing downstream ever saw it, so
 * neither composer wrote anything down about it. It joins where the way does, which is why the
 * question "was anything left out" is asked of {@link #reconciledWith} and cannot be asked of this
 * alone — a predicate here would answer it for the two composers and be read as the answer for the
 * way.
 *
 * @param onTheWay          what the search could not compose against of the way it was given, which
 *                          is about the values that search writes. A search for an answer of a
 *                          dependency is one of those too, and its caller is where what it came to
 *                          becomes a shortfall about a demand
 * @param onAnAnswer        what the values standing the dependencies in were not composed against
 * @param takenUpByAnAnswer the conditions the demand reading answered for, whether it stated them
 *                          or wrote down that it could not, named the way the reading names a
 *                          condition. Not by where a report about one points: a helper expanded
 *                          twice puts two conditions in a body and both are written in one place,
 *                          so a join on the place would let what became of one answer for the other
 */
public record CompositionAccount(List<ReachabilityGap> onTheWay,
                                 List<DemandGap> onAnAnswer,
                                 Set<ConditionOccurrence> takenUpByAnAnswer) {

    /** A composition that left nothing out, which is what a caller with no dependencies and every
     *  condition composed against has. */
    public static final CompositionAccount NOTHING =
            new CompositionAccount(List.of(), List.of(), Set.of());

    public CompositionAccount {
        onTheWay = List.copyOf(onTheWay);
        onAnAnswer = List.copyOf(onAnAnswer);
        takenUpByAnAnswer = Set.copyOf(takenUpByAnAnswer);
    }

    /** One of a search whose way asked nothing of any answer. */
    public static CompositionAccount ofTheInput(List<ReachabilityGap> onTheWay) {
        return onTheWay.isEmpty() ? NOTHING
                : new CompositionAccount(onTheWay, List.of(), Set.of());
    }

    /**
     * This account with what the answer side came to put on it.
     *
     * <p>The one that has something is the answer where the other has nothing, which is what
     * almost every composing is: a behavior requiring nothing asks nothing of any answer, and a
     * search that composed against everything it was handed leaves nothing on either side. Built
     * out of both regardless, every attempt of every point would copy three collections to say so.
     */
    public CompositionAccount and(CompositionAccount answers) {
        if (answers.isNothing()) {
            return this;
        }
        if (isNothing()) {
            return answers;
        }
        List<ReachabilityGap> input = new ArrayList<>(onTheWay);
        input.addAll(answers.onTheWay);
        List<DemandGap> demands = new ArrayList<>(onAnAnswer);
        demands.addAll(answers.onAnAnswer);
        Set<ConditionOccurrence> taken = new LinkedHashSet<>(takenUpByAnAnswer);
        taken.addAll(answers.takenUpByAnAnswer);
        return new CompositionAccount(input, demands, taken);
    }

    /**
     * What this composing and another of the same way went without, between them.
     *
     * <p>For an answer made of several composings, none of which is the answer alone: a condition
     * either went without is one the answer is weaker for. So what either could not compose against
     * is kept, and a condition counts as taken up by an answer only where both took it up — one
     * that only the other took up is one this composing went without, and reconciled against the
     * way it is a gap ({@link #reconciledWith}). What comes out reconciles to every gap either of
     * the two reconciles to, and to no other.
     *
     * <p>Each gap once, in the order this then the other met them.
     */
    public CompositionAccount alongside(CompositionAccount other) {
        List<ReachabilityGap> input = new ArrayList<>(new LinkedHashSet<>(onTheWay));
        other.onTheWay.stream().filter(each -> !input.contains(each)).forEach(input::add);
        List<DemandGap> demands = new ArrayList<>(new LinkedHashSet<>(onAnAnswer));
        other.onAnAnswer.stream().filter(each -> !demands.contains(each)).forEach(demands::add);
        Set<ConditionOccurrence> taken = new LinkedHashSet<>(takenUpByAnAnswer);
        taken.retainAll(other.takenUpByAnAnswer);
        return new CompositionAccount(input, demands, taken);
    }

    /**
     * This account with a figure said to be why the statements about an answer that name a number
     * of the input were not composed against.
     *
     * <p>Only those: a statement that names no such number was not composed against for a reason
     * that is not the looking over a number's values, and a figure said of it would send a reader
     * to raise something that changes nothing.
     */
    public CompositionAccount sayingAFigureEndedTheLookingOverNumbers(
            Set<CompositionBudget> figures) {
        List<DemandGap> said = new ArrayList<>();
        for (DemandGap each : onAnAnswer) {
            said.add(each instanceof DemandGap.Uncomposed(
                    AnswerDemand.AStatement statement, var why)
                    && !(why instanceof DemandGap.WhyNotComposed.NoPairComposedBeforeAFigureEnded)
                    && !(why instanceof DemandGap.WhyNotComposed.NoWayComposedBeforeAFigureEnded)
                    && !AnswerAsAnInput.inputNumbersIn(statement.statement()).isEmpty()
                    ? new DemandGap.Uncomposed(statement,
                            DemandGap.WhyNotComposed.NoPairComposedBeforeAFigureEnded.by(figures))
                    : each);
        }
        return new CompositionAccount(onTheWay, said, takenUpByAnAnswer);
    }

    /** Whether this says nothing at all, which is a composing with nothing written down on either
     *  side and no condition of an answer to have answered for. */
    private boolean isNothing() {
        return onTheWay.isEmpty() && onAnAnswer.isEmpty() && takenUpByAnAnswer.isEmpty();
    }

    /**
     * Everything the row was composed without, as one list in the order a reader meets it.
     *
     * <p>The way's own declines first, then what each projection stated and could not act on. A
     * condition the walk had no words for is one nothing downstream ever saw, and it is read before
     * the answers of the stages that did see something.
     *
     * <p><b>A decline of the input projection is not a gap where the answer projection took the
     * condition up.</b> The input reading declines every condition about an answer — it has no
     * position to read one at — so such a decline says which projection the condition belongs to
     * rather than that anything was missed. What became of it is the answer side's to say, and it
     * is in this list wherever that side has something to report.
     */
    public List<ConditionGap> reconciledWith(WayToTheBorder way) {
        List<ConditionGap> out = new ArrayList<>();
        for (OnTheWay.Declined each : way.declined()) {
            if (!takenUpByAnAnswer.contains(each.condition())) {
                out.add(new ConditionGap.OfTheInput(new ReachabilityGap.Unstated(each)));
            }
        }
        onTheWay.forEach(each -> out.add(new ConditionGap.OfTheInput(each)));
        onAnAnswer.forEach(each -> out.add(new ConditionGap.OfADemand(each)));
        return List.copyOf(out);
    }
}
