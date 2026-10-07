package souther.compiler.partition;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.UnaryOperator;

/**
 * The conditions one way through a body consulted, in the order it met them.
 *
 * <p>What a decision rule is made of, as the reading of the ways writes a path. Held as a value
 * because two ways that consulted the same distinctions and got the same answers are one way — which
 * is what lets the reading count what the body does rather than how it got there.
 *
 * <p><b>One column per distinction, however often the path meets it.</b> A body asking one thing
 * twice states one distinction, and a column apiece would admit an assignment where it holds and
 * does not. So a second reading of a column already on the path is dropped where it agrees, and the
 * whole path is refused where it does not — a path assuming a proposition both ways is a
 * contradiction rather than a rule, and refusing it here is what the reading of the ways does with
 * one.
 */
final class DecisionPath {

    /** A path that has consulted nothing, which is what a value nothing forks arrives by. */
    static final DecisionPath NOWHERE = new DecisionPath(List.of());

    private final List<Consulted> consulted;

    /**
     * The rule this path is, made once.
     *
     * <p>Held rather than worked out per call, which is why this is a class and not a record. What
     * tells two paths apart is the rule, so the walk that gathers the ways asks for it once per
     * candidate per way already gathered — and a rule built from the columns each time made the
     * cost of reading one body's ways grow with their square.
     *
     * <p>Made in the constructor rather than on first use. The value is what this is, and a field
     * filled later is a value that answers differently before and after somebody asks.
     */
    private final DecisionRule rule;

    DecisionPath(List<Consulted> consulted) {
        this.consulted = List.copyOf(consulted);
        Map<DecisionCondition, DecidedCondition> vector = new LinkedHashMap<>();
        this.consulted.forEach(each -> vector.put(each.answer().condition(), each.answer()));
        this.rule = new DecisionRule(vector);
    }

    /** The conditions this path consulted, in the order it met them. */
    List<Consulted> consulted() {
        return consulted;
    }

    /**
     * One condition this path consulted: what it came out as, where a run through it is seen, and
     * what it states about the input.
     *
     * <p>Only the first is part of what the path is. Which distinctions a rule turns on is what
     * tells it from another rule; where each of them is written is what joins it to a run, and what
     * it states is what a search composes a row against.
     *
     * @param states the condition in the words a composer of a row already works from, so that a
     *               column of a decision table and the region a row for it is looked for in cannot
     *               be read off two accounts of one comparison. As many as the condition asks of a
     *               row — every element of a list meeting two things is two relations and one
     *               column — and all of them about the one condition
     */
    record Consulted(DecidedCondition answer, ShownBy shown, List<OnTheWay> states) {

        Consulted {
            if (answer == null || shown == null || states == null || states.isEmpty()) {
                throw new IllegalArgumentException("a condition a path consulted is an answer,"
                        + " where it is seen, and what it states");
            }
            states = List.copyOf(states);
        }

        /** Where a report about the condition asks for its place, which every entry for it
         *  shares. */
        ConditionReportAnchor anchor() {
            return states.getFirst().anchor();
        }
    }

    /** This path with {@code answer} on it, or null where the path already answers that column the
     *  other way. */
    DecisionPath and(DecidedCondition answer, ShownBy shown, List<OnTheWay> states) {
        return and(new DecisionPath(List.of(new Consulted(answer, shown, states))));
    }

    /**
     * Two paths are one where they are the same rule.
     *
     * <p>Which is what the reading of the ways asks of a path: two that stand for the same way are
     * equal, so a way found twice is one way. What a rule is is its columns and what each came out
     * as — {@link DecisionRule}'s answer, and asked of it rather than worked out again here, so
     * that a path and the rule it is cannot be told apart by different rules.
     *
     * <p>Which makes it the order-independent answer the rule is. The order the walk met the
     * conditions in is kept for a reader and is no part of what a rule is: two ways that consulted
     * the same distinctions and got the same answers are one rule whatever order they met them in,
     * and holding them apart by that order would count what the reading did rather than what the
     * body does.
     */
    @Override
    public boolean equals(Object other) {
        return other instanceof DecisionPath that && rule.equals(that.rule);
    }

    @Override
    public int hashCode() {
        return rule.hashCode();
    }

    /** What this path states about the input, which is what a search composes a row against. */
    WayToTheBorder states() {
        return new WayToTheBorder(consulted.stream()
                .flatMap(each -> each.states().stream()).toList());
    }

    /**
     * What this path asks of the answers a row stands the dependencies in with.
     *
     * <p>Read here, where what a condition came out as and where a report about it asks for its
     * place are one entry. Worked out from the rule alone, a demand would have no anchor and the
     * one it was given would be whichever the two lists happened to line up at.
     */
    AnswersDemanded demands() {
        List<AnswerDemand> stated = new ArrayList<>();
        List<DemandGap.Unstated> declined = new ArrayList<>();
        Set<ConditionOccurrence> takenUp = new LinkedHashSet<>();
        for (Consulted each : consulted) {
            Asked asked = asked(each);
            switch (asked) {
                case Asked.Stated(var demand) -> stated.add(demand);
                case Asked.NotStated(var why) ->
                        declined.add(new DemandGap.Unstated(each.anchor(), why));
                case Asked.OfTheInput _ -> { }
            }
            // Which condition it is, the way the reading names one, and taken off the walk's own
            // entry for the same consulted condition. A decline is the only entry that names one,
            // and it is the only entry this has anything to reconcile with: what the walk took in
            // it took in, and there is nothing there for the answer side to answer for.
            if (!(asked instanceof Asked.OfTheInput)) {
                for (OnTheWay state : each.states()) {
                    if (state instanceof OnTheWay.Declined left) {
                        takenUp.add(left.condition());
                    }
                }
            }
        }
        return stated.isEmpty() && declined.isEmpty()
                ? AnswersDemanded.NOTHING : new AnswersDemanded(stated, declined, takenUp);
    }

    /**
     * What one consulted condition asks of an answer.
     *
     * <p>Three answers and not a demand beside an absence. A condition about the input alone asks
     * nothing of any answer and a condition about an answer this cannot state is a shortfall of
     * this reading, and an absence standing for both is a second reading of the same column
     * deciding which it was — two answers to one question with nothing holding them together.
     */
    private sealed interface Asked {

        /** What a value standing the dependency in has to satisfy. */
        record Stated(AnswerDemand demand) implements Asked {}

        /** A condition about an answer this reading has no way of putting to a composer. */
        record NotStated(DemandGap.WhyNotStated why) implements Asked {}

        /** A condition about the input alone, which this side has nothing to say about. */
        record OfTheInput() implements Asked {}
    }

    private static final Asked OF_THE_INPUT = new Asked.OfTheInput();

    private static Asked asked(Consulted one) {
        ConditionReportAnchor anchor = one.anchor();
        return switch (one.answer()) {
            case DecidedCondition.Narrowed(var condition, var to) ->
                    condition.of() instanceof DecisionSubject.AnAnswer at
                            ? new Asked.Stated(
                                    new AnswerDemand.ACase(at.answered(), anchor, at.steps(), to))
                            : OF_THE_INPUT;
            // A truth of the answer itself, or of a place inside one: the value the answer is, or
            // the value written at that place where the answer is composed.
            case DecidedCondition.Stood(var condition, var held) ->
                    condition.of() instanceof DecisionSubject.AnAnswer at
                            ? new Asked.Stated(new AnswerDemand.ATruth(at.answered(), anchor,
                                    at.steps(), held))
                            : OF_THE_INPUT;
            case DecidedCondition.Compared(var condition, var held) -> switch (condition) {
                case DecisionCondition.AComparison it -> compared(it, held, anchor);
                // A place on a carrier's own order, which is a value and not a form. What this
                // stage composes against an answer is a form, so a column of that shape is left
                // unstated here for the reason a form over two answers is.
                case DecisionCondition.AnOrderedComparison(var term, var _, var _) ->
                        term instanceof DecisionAtom.OfAnAnswer
                                ? new Asked.NotStated(
                                        new DemandGap.WhyNotStated.APlaceOnTheAnswersOwnOrder())
                                : OF_THE_INPUT;
            };
            case DecidedCondition.Unread _ -> OF_THE_INPUT;
        };
    }

    /**
     * A comparison as a demand on one answer, or what stopped it from being one.
     *
     * <p>Of one answer and of nothing beside it. A form over two answers, or over an answer and a
     * number of the input, is one statement about the pair and nothing here composes two values to
     * it together — so it is left unstated, which is what a way carries as a condition a row may
     * not satisfy rather than as one that is not there.
     *
     * <p>A form naming no answer at all is neither of those. It is the input's, and this side has
     * nothing to say about it.
     */
    private static Asked compared(DecisionCondition.AComparison condition, boolean held,
                                  ConditionReportAnchor anchor) {
        InjectedAnswer only = null;
        boolean anyOfAnAnswer = false;
        boolean everyAtomIsOfIt = true;
        for (DecisionAtom atom : condition.form().coefs().keySet()) {
            if (!(atom instanceof DecisionAtom.OfAnAnswer(var at))) {
                everyAtomIsOfIt = false;
                continue;
            }
            anyOfAnAnswer = true;
            if (only != null && !only.equals(at.answered())) {
                everyAtomIsOfIt = false;
                break;
            }
            only = at.answered();
        }
        if (!anyOfAnAnswer) {
            return OF_THE_INPUT;
        }
        if (!everyAtomIsOfIt) {
            return new Asked.NotStated(
                    new DemandGap.WhyNotStated.AFormOverMoreThanOneAnswer());
        }
        // The side the path took, which is what a row has to satisfy. The column faces the way its
        // proposition does whichever side was taken, so the denial is taken here rather than left
        // for a composer to work out from a flag travelling beside the form.
        return new Asked.Stated(new AnswerDemand.AComparison(only, anchor, condition.form(),
                held ? condition.proposition() : condition.proposition().denied()));
    }

    /** Both paths' conditions, or null where between them they answer one column two ways. */
    DecisionPath and(DecisionPath more) {
        List<Consulted> out = new ArrayList<>(consulted);
        for (Consulted each : more.consulted) {
            Consulted already = at(out, each.answer().condition());
            if (already == null) {
                out.add(each);
            } else if (!already.answer().equals(each.answer())) {
                return null;
            }
        }
        return new DecisionPath(out);
    }

    /**
     * This path with where each condition is seen answered again by {@code seen}, for a path a run
     * is known by more than its conditions to have taken.
     *
     * <p>The same rule: where a run through a condition is seen is no part of what the rule is.
     */
    DecisionPath seenAgain(UnaryOperator<ShownBy> seen) {
        List<Consulted> out = new ArrayList<>();
        for (Consulted each : consulted) {
            out.add(new Consulted(each.answer(), seen.apply(each.shown()), each.states()));
        }
        return new DecisionPath(out);
    }

    /** What this path says about {@code condition}, or null where it never consulted it. */
    private static Consulted at(List<Consulted> consulted, DecisionCondition condition) {
        for (Consulted each : consulted) {
            if (each.answer().condition().equals(condition)) {
                return each;
            }
        }
        return null;
    }

    /** The rule this path is, which is its columns and what each came out as. */
    DecisionRule rule() {
        return rule;
    }

    /** Where a run down this path is seen, one entry per column in the order it met them. */
    List<ShownBy> shownBy() {
        return consulted.stream().map(Consulted::shown).toList();
    }
}
