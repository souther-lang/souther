package souther.compiler.partition;

import souther.compiler.meaning.AnswerAsAnInput;

import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
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
     * <p>Each gap once, in the order this then the other met them — which is the order the two
     * were put together in, so a caller with more than one composing to put together puts what
     * comes out in an order of the model's ({@link #inTheOrderOf}).
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
     * This account with what it went without in an order of the model's.
     *
     * <p>For an account several composings were put together into. What each went without is in
     * the order that composing met it, and putting them together leaves the order they were put
     * together in — which is the order the composings were made in, and that is this compiler's
     * walk and nothing a reader can find in the source.
     *
     * <p>By what each gap is about, in the order the reading states it: the conditions on the way,
     * then what the way asks of an answer, then what it could not state of one. By what it is about
     * and not by where a report sends a reader for it, which is one place for every call of a
     * helper and would leave the gaps of two calls in the order they were put together in.
     *
     * <p>And two gaps about one thing by what each says, in the order their shapes are declared
     * ({@link #rankOf(ReachabilityGap)}, {@link #rankOf(DemandGap)}). Two composings may go without
     * one condition for two reasons, and which a reader meets first is not the walk's to decide.
     * Whatever two such gaps say beyond their shape and their figures is about the condition's
     * reading, which is the same along every way, so the order is total over what can come back.
     *
     * <p>A gap about something the reading did not state comes after the rest.
     *
     * @param way     the way the composings were made along
     * @param demands what the way asks of the answers, and what it could not state of them
     */
    public CompositionAccount inTheOrderOf(WayToTheBorder way, AnswersDemanded demands) {
        List<ReachabilityGap> input = new ArrayList<>(onTheWay);
        input.sort(Comparator.comparingInt((ReachabilityGap gap) ->
                        placeIn(way.onTheWay(), aboutOf(gap)))
                .thenComparing(CompositionAccount::rankOf, LEXICALLY)
                .thenComparing(CompositionAccount::figuresOf,
                        published(PublicationOrders.COMPOSITION_BUDGETS))
                .thenComparing(CompositionAccount::populationsOf,
                        published(PublicationOrders.COMPOSITION_REPERTOIRES))
                .thenComparing(CompositionAccount::unheldOf,
                        published(PublicationOrders.COMPOSITION_CAPACITIES)));
        List<Object> asked = new ArrayList<>(demands.stated());
        asked.addAll(demands.declined());
        List<DemandGap> answers = new ArrayList<>(onAnAnswer);
        answers.sort(Comparator.comparingInt((DemandGap gap) -> placeIn(asked, switch (gap) {
                    case DemandGap.Uncomposed it -> it.demand();
                    case DemandGap.Unstated it -> it;
                }))
                .thenComparing(CompositionAccount::rankOf, LEXICALLY)
                .thenComparing(CompositionAccount::figuresOf,
                        published(PublicationOrders.COMPOSITION_BUDGETS)));
        return new CompositionAccount(input, answers, takenUpByAnAnswer);
    }

    private static final Comparator<List<Integer>> LEXICALLY = (one, other) -> {
        for (int i = 0; i < Math.min(one.size(), other.size()); i++) {
            int at = Integer.compare(one.get(i), other.get(i));
            if (at != 0) {
                return at;
            }
        }
        return Integer.compare(one.size(), other.size());
    };

    /**
     * Two lists of one kind of reason, compared in the order that kind is published in.
     *
     * <p>Asked of the order and never worked out here: the first place the two differ is decided by
     * which of the two the order says first, so what a reader meets first is what every other
     * reader of the kind says first.
     */
    private static <T> Comparator<List<T>> published(CanonicalSelection.Order<T> order) {
        return (one, other) -> {
            for (int i = 0; i < Math.min(one.size(), other.size()); i++) {
                T mine = one.get(i);
                T theirs = other.get(i);
                if (!Objects.equals(mine, theirs)) {
                    return Objects.equals(order.keep(List.of(mine, theirs)).written().getFirst(),
                            mine) ? -1 : 1;
                }
            }
            return Integer.compare(one.size(), other.size());
        };
    }

    private static List<CompositionBudget> figuresOf(ReachabilityGap gap) {
        return switch (gap) {
            case ReachabilityGap.Uncomposed(var _,
                    ReachabilityGap.Why.TheWalkForItsPositionsWasStopped stopped) ->
                    stopped.by().written();
            case ReachabilityGap.LookedAlongWhole it -> List.of(it.figure());
            case ReachabilityGap.Unstated _, ReachabilityGap.Uncomposed _,
                 ReachabilityGap.ProvedImpossible _ -> List.of();
        };
    }

    private static List<CompositionRepertoire> populationsOf(ReachabilityGap gap) {
        return gap instanceof ReachabilityGap.Uncomposed(var _,
                ReachabilityGap.Why.TheWalkForItsPositionsWasStopped stopped)
                ? stopped.writes().written() : List.of();
    }

    private static List<CompositionCapacity> unheldOf(ReachabilityGap gap) {
        return gap instanceof ReachabilityGap.Uncomposed(var _,
                ReachabilityGap.Why.TheWalkForItsPositionsWasStopped stopped)
                ? stopped.unheld().written() : List.of();
    }

    private static List<CompositionBudget> figuresOf(DemandGap gap) {
        return switch (gap) {
            case DemandGap.Uncomposed(var _,
                    DemandGap.WhyNotComposed.NoPairComposedBeforeAFigureEnded ended) ->
                    ended.figures().written();
            case DemandGap.Uncomposed(var _,
                    DemandGap.WhyNotComposed.NoWayComposedBeforeAFigureEnded ended) ->
                    ended.figures().written();
            case DemandGap.Uncomposed _, DemandGap.Unstated _ -> List.of();
        };
    }

    private static int placeIn(List<?> stated, Object what) {
        int at = stated.indexOf(what);
        return at < 0 ? stated.size() : at;
    }

    private static OnTheWay aboutOf(ReachabilityGap gap) {
        return switch (gap) {
            case ReachabilityGap.Unstated it -> it.condition();
            case ReachabilityGap.Uncomposed it -> it.condition();
            case ReachabilityGap.LookedAlongWhole it -> it.condition();
            case ReachabilityGap.ProvedImpossible it -> it.condition();
        };
    }

    /**
     * What a gap on the way says, as numbers in the order its shapes are declared: the shape, then
     * the shape of its reason. The figures it names are asked of the order they are published in
     * ({@link #published}), which is theirs to give.
     */
    private static List<Integer> rankOf(ReachabilityGap gap) {
        List<Integer> out = new ArrayList<>();
        switch (gap) {
            case ReachabilityGap.Unstated _ -> out.add(0);
            case ReachabilityGap.Uncomposed it -> {
                out.add(1);
                switch (it.why()) {
                    case ReachabilityGap.Why.NoValueComposedForItsPositions _ -> out.add(0);
                    case ReachabilityGap.Why.TheWalkForItsPositionsWasStopped _ -> out.add(1);
                    case ReachabilityGap.Why.TwoNumbersAtOneLocation _ -> out.add(2);
                    case ReachabilityGap.Why.NoComposerWritesIt none -> {
                        out.add(3);
                        out.add(none.what().ordinal());
                    }
                    case ReachabilityGap.Why.ElementsWrittenAlike _ -> out.add(4);
                }
            }
            case ReachabilityGap.LookedAlongWhole _ -> out.add(2);
            case ReachabilityGap.ProvedImpossible _ -> out.add(3);
        }
        return out;
    }

    /** The same, of a gap about an answer. */
    private static List<Integer> rankOf(DemandGap gap) {
        List<Integer> out = new ArrayList<>();
        switch (gap) {
            case DemandGap.Unstated it -> {
                out.add(0);
                out.add(switch (it.why()) {
                    case DemandGap.WhyNotStated.AFormOverMoreThanOneAnswer _ -> 0;
                    case DemandGap.WhyNotStated.APlaceOnTheAnswersOwnOrder _ -> 1;
                    case DemandGap.WhyNotStated.AStatementOfSeveralParts _ -> 2;
                });
            }
            case DemandGap.Uncomposed it -> {
                out.add(1);
                switch (it.why()) {
                    case DemandGap.WhyNotComposed.NoOrderUnderATermOfTheAnswer _ -> out.add(0);
                    case DemandGap.WhyNotComposed.NoValueComposedAtItsPositions _ -> out.add(1);
                    case DemandGap.WhyNotComposed.NothingComposedAValueOfTheAnswer _ -> out.add(2);
                    case DemandGap.WhyNotComposed.OneValueAnswersEveryCall _ -> out.add(3);
                    case DemandGap.WhyNotComposed.NoPairComposedBeforeAFigureEnded _ -> out.add(4);
                    case DemandGap.WhyNotComposed.NoWayComposedBeforeAFigureEnded _ -> out.add(5);
                }
            }
        }
        return out;
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
