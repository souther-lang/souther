package souther.compiler.partition;

import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.TermPath;
import souther.compiler.inputs.TraversalDirection;
import souther.compiler.meaning.AnswerAsAnInput;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.InjectedAnswer;
import souther.compiler.meaning.Proposition;

import java.util.ArrayList;
import java.util.HashSet;
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
 * does not. So a second reading of a column already on the path is that column consulted again
 * where it agrees — one column, with where each consultation was and what it was read off — and the
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
     * One condition this path consulted: what it came out as, every place a run through it is
     * seen on the way, and what it states about the input.
     *
     * <p>Only the first is part of what the path is. Which distinctions a rule turns on is what
     * tells it from another rule; where each of them is written is what joins it to a run, and what
     * it states is what a search composes a row against.
     *
     * <p><b>One column, met as often as the way meets it.</b> A helper called twice on one way asks
     * one thing twice: one distinction of the rule, consulted at two calls. The column is one, and
     * what each consultation was is kept beside it — dropped, a rule through both calls would be
     * described by one of them.
     *
     * @param seen   every place a run through the condition is seen on the way, in the order the
     *               way met them; never empty. The first is where the column is witnessed, since
     *               a run that took the way went through it there
     * @param states the condition in the words a composer of a row already works from, so that a
     *               column of a decision table and the region a row for it is looked for in cannot
     *               be read off two accounts of one comparison. As many as the condition asks of a
     *               row — every element of a list meeting two things is two relations and one
     *               column — and all of them about the one condition
     * @param said   which copies of the model's code each of {@code states} was read off, told
     *               where the condition was read, at every place it was consulted
     * @param cases  what a row has to be, beside the way, to be evidence of a case the condition's
     *               statement draws inside itself. One column asks one thing, so these are the
     *               first consultation's
     */
    record Consulted(DecidedCondition answer, List<ShownBy> seen, List<OnTheWay> states,
                     SaidOnTheWay said, List<CaseWay> cases) {

        Consulted {
            cases = List.copyOf(cases);
            if (answer == null || seen == null || seen.isEmpty() || states == null
                    || states.isEmpty() || said == null) {
                throw new IllegalArgumentException("a condition a path consulted is an answer,"
                        + " where it is seen, what it states and what that was read off");
            }
            seen = List.copyOf(seen);
            states = List.copyOf(states);
        }

        /** The condition consulted once, seen at {@code shown}, drawing the cases {@code cases}. */
        Consulted(DecidedCondition answer, ShownBy shown, List<OnTheWay> states,
                  SaidOnTheWay said, List<CaseWay> cases) {
            this(answer, List.of(shown), states, said, cases);
        }

        /** Where the column is witnessed: the first place the way met it. */
        ShownBy shown() {
            return seen.getFirst();
        }

        /**
         * The same column, consulted again as {@code more} was.
         *
         * <p>What it states is what it states the first time — one column asks one thing — and
         * what each consultation was read off is told of it, entry for the entry it asked the
         * first time ({@link SaidOnTheWay#retold}), so a gap about it names every call that asked
         * it.
         */
        Consulted again(Consulted more) {
            // Consulted again as itself it is told of no place and no copy it was not already, and
            // telling it walks every entry on the way to find that out.
            if (more == this) {
                return this;
            }
            List<ShownBy> places = new ArrayList<>(seen);
            more.seen.stream().filter(each -> !places.contains(each)).forEach(places::add);
            return new Consulted(answer, places, states,
                    said.retold(states, more.states, more.said), cases);
        }

        /** Where a report about the condition asks for its place, which every entry for it
         *  shares. */
        ConditionReportAnchor anchor() {
            return states.getFirst().anchor();
        }
    }

    /** This path with {@code answer} on it, or null where the path already answers that column the
     *  other way. */
    DecisionPath and(DecidedCondition answer, ShownBy shown, List<OnTheWay> states,
                     SaidOnTheWay said, List<CaseWay> cases) {
        return and(new DecisionPath(List.of(new Consulted(answer, shown, states, said, cases))));
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

    /**
     * Each condition this path consulted, with what it states about the input and asks of the
     * answers, in the order the walk met them.
     *
     * <p>What a rule's way states and asks is these one after another; kept apart here, so that what
     * a search goes without can be traced to the condition that said it.
     */
    List<RuleStep> steps() {
        List<RuleStep> out = new ArrayList<>();
        for (Consulted each : consulted) {
            AnswersDemanded demands = demands(each);
            out.add(new RuleStep(each.seen(), each.states(), demands,
                    each.said().asking(demands), each.cases()));
        }
        return List.copyOf(out);
    }

    /**
     * What one consulted condition asks of the answers a row stands the dependencies in with.
     *
     * <p>Read here, where what a condition came out as and where a report about it asks for its
     * place are one entry. Worked out from the rule alone, a demand would have no anchor and the
     * one it was given would be whichever the two lists happened to line up at.
     */
    private static AnswersDemanded demands(Consulted each) {
        List<AnswerDemand> stated = new ArrayList<>();
        List<DemandGap.Unstated> declined = new ArrayList<>();
        Set<ConditionOccurrence> takenUp = new LinkedHashSet<>();
        Asked asked = asked(each);
        switch (asked) {
            case Asked.Stated(var demand) -> stated.add(demand);
            case Asked.NotStated(var why) ->
                    declined.add(new DemandGap.Unstated(each.anchor(), why));
            case Asked.OfTheInput _ -> { }
        }
        // Which condition it is, the way the reading names one, and taken off the walk's own entry
        // for the same consulted condition. A decline is the only entry that names one, and it is
        // the only entry this has anything to reconcile with: what the walk took in it took in, and
        // there is nothing there for the answer side to answer for.
        if (!(asked instanceof Asked.OfTheInput)) {
            for (OnTheWay state : each.states()) {
                if (state instanceof OnTheWay.Declined left) {
                    takenUp.add(left.condition());
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
                case DecisionCondition.AComparison it -> compared(it, held, one);
                // A place on a carrier's own order, which is a value and not a form. What this
                // stage composes against an answer is a form, so a column of that shape is left
                // unstated here for the reason a form over two answers is.
                case DecisionCondition.AnOrderedComparison(var term, var _, var _) ->
                        term instanceof DecisionAtom.OfAnAnswer
                                ? new Asked.NotStated(
                                        new DemandGap.WhyNotStated.APlaceOnTheAnswersOwnOrder())
                                : OF_THE_INPUT;
            };
            // A statement of several parts: the input's where it is about nothing a dependency
            // answered, and otherwise one this side composes no value to whole.
            case DecidedCondition.Held(var condition, var held) -> {
                if (!Proposition.aboutAnAnswer(condition.statement())) {
                    yield OF_THE_INPUT;
                }
                // The side the path took, as a comparison's is: what a row has to satisfy is that,
                // and not the column's own reading.
                Proposition taken = held ? condition.statement() : condition.statement().denied();
                InjectedAnswer only = AnswerAsAnInput.onlyAnswerIn(taken);
                yield only == null
                        ? new Asked.NotStated(
                                new DemandGap.WhyNotStated.AStatementOfSeveralParts())
                        : new Asked.Stated(new AnswerDemand.AStatement(only, anchor, taken,
                                takenIn(one.states())));
            }
            case DecidedCondition.Unread _ -> OF_THE_INPUT;
        };
    }

    /**
     * A comparison as a demand on the value a row stands one dependency in with, or what stopped
     * it from being one.
     *
     * <p>Of one dependency and of nothing beside it. A row writes one value for a dependency, which
     * answers every call of it, so a form over places of what two calls answered is a form over
     * places of that one value — {@code look(at).k == look(at).j} asks for a value whose two fields
     * agree. Not where two calls read one place: that is the value held against itself, which two
     * answers are not, and it is left as what it says.
     *
     * <p>A form over two dependencies is one statement about the pair and nothing here composes two
     * values to it together — so it is left unstated, which is what a way carries as a condition a
     * row may not satisfy rather than as one that is not there. A form over an answer and a number
     * of the input is a statement of the answer: the number is put at a value the way leaves it, and
     * the answer composed for that ({@link InputNumbersAnAnswerTurnsOn}).
     *
     * <p>A form naming no answer at all is neither of those. It is the input's, and this side has
     * nothing to say about it.
     */
    private static Asked compared(DecisionCondition.AComparison condition, boolean held,
                                  Consulted one) {
        ConditionReportAnchor anchor = one.anchor();
        InjectedAnswer only = null;
        Set<Place> places = new HashSet<>();
        boolean anyOfAnAnswer = false;
        boolean namesTheInput = false;
        for (DecisionAtom atom : condition.form().coefs().keySet()) {
            DecisionSubject.AnAnswer at = atom.ofTheAnswer();
            if (at == null) {
                namesTheInput = true;
                continue;
            }
            anyOfAnAnswer = true;
            if ((only != null && !only.dependency().equals(at.answered().dependency()))
                    || !places.add(placeOf(atom, at))) {
                return new Asked.NotStated(
                        new DemandGap.WhyNotStated.AFormOverMoreThanOneAnswer());
            }
            only = only == null ? at.answered() : only;
        }
        if (!anyOfAnAnswer) {
            return OF_THE_INPUT;
        }
        // A number of the input beside the answer's is a statement about the pair, which is met by
        // putting that number at a value and composing the answer for it, as any statement that
        // names one is.
        if (namesTheInput) {
            return new Asked.Stated(new AnswerDemand.AStatement(only, anchor,
                    AnswerAsAnInput.ofAComparison(condition.form(), condition.proposition(),
                            held), takenIn(one.states())));
        }
        // The side the path took, which is what a row has to satisfy. The column faces the way its
        // proposition does whichever side was taken, so the denial is taken here rather than left
        // for a composer to work out from a flag travelling beside the form.
        return new Asked.Stated(new AnswerDemand.AComparison(only, anchor, condition.form(),
                held ? condition.proposition() : condition.proposition().denied()));
    }

    /**
     * What the way took in of one condition, inside every alternative it came out as: the entries
     * a reading of it put on the way, which a search of one alternative holds some of.
     */
    private static List<OnTheWay.TakenIn> takenIn(List<OnTheWay> states) {
        List<OnTheWay.TakenIn> out = new ArrayList<>();
        for (OnTheWay each : states) {
            switch (each) {
                case OnTheWay.TakenIn taken -> out.add(taken);
                case OnTheWay.OneOf several ->
                        several.alternatives().forEach(way -> out.addAll(takenIn(way)));
                // Which of the statements counted hold is no entry a search of one alternative
                // holds the row to.
                case OnTheWay.Narrowed _, OnTheWay.Settled _, OnTheWay.Declined _,
                     OnTheWay.Counted _ -> { }
            }
        }
        return out;
    }

    /**
     * A place inside an answer, and how a number is taken of it where one is taken: the place read
     * as itself and the same place counted are two numbers.
     *
     * <p>Not which evaluation of the dependency it is. A row writes one value for a dependency,
     * so two calls reading one place read the value held against itself.
     */
    private record Place(ValueName.Stdlib operation, TakenArguments arguments,
                         List<TermPath.Step> steps, Computed computed) {}

    /** What a total that turns on where each element stands is a total of, beside the place of
     *  the list: the computation, what it stands as, and the direction the elements are handed
     *  in. Two such totals of one list are two numbers. The answer itself is not part of it, since
     *  which call of the dependency it is has no part in which value a row writes. */
    private record Computed(ElementValue computation, Type each, TraversalDirection direction) {}

    private static Place placeOf(DecisionAtom atom, DecisionSubject.AnAnswer at) {
        return switch (atom) {
            case DecisionAtom.TakenOfAnAnswer taken ->
                    new Place(taken.operation(), taken.arguments(), at.steps(), null);
            case DecisionAtom.ComputedOverAnAnswer computed ->
                    new Place(computed.operation(), TakenArguments.NONE, at.steps(),
                            new Computed(computed.computation(), computed.each(),
                                    computed.direction()));
            case DecisionAtom.OfAnAnswer _, DecisionAtom.OfTheInput _ ->
                    new Place(null, null, at.steps(), null);
        };
    }

    /**
     * Both paths' conditions, or null where between them they answer one column two ways.
     *
     * <p>A column both answer alike is one column, consulted again ({@link Consulted#again}).
     */
    DecisionPath and(DecisionPath more) {
        // Refused by the rules first: each is what its path's columns came out as, so the two
        // disagree exactly where a column of one came out otherwise in the other. Most ways a
        // reading pairs are ways no run takes, and each of those is answered by a look per column
        // rather than by finding every condition of one among the conditions of the other.
        for (Map.Entry<DecisionCondition, DecidedCondition> each
                : more.rule.consulted().entrySet()) {
            DecidedCondition had = rule.at(each.getKey());
            if (had != null && !had.equals(each.getValue())) {
                return null;
            }
        }
        List<Consulted> out = new ArrayList<>(consulted);
        for (Consulted each : more.consulted) {
            int already = at(out, each.answer().condition());
            if (already < 0) {
                out.add(each);
            } else if (!out.get(already).answer().equals(each.answer())) {
                return null;
            } else {
                out.set(already, out.get(already).again(each));
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
            out.add(new Consulted(each.answer(), each.seen().stream().map(seen).toList(),
                    each.states(), each.said(), each.cases()));
        }
        return new DecisionPath(out);
    }

    /** Where this path consulted {@code condition}, or -1 where it never did. */
    private static int at(List<Consulted> consulted, DecisionCondition condition) {
        for (int each = 0; each < consulted.size(); each++) {
            if (consulted.get(each).answer().condition().equals(condition)) {
                return each;
            }
        }
        return -1;
    }

    /** The rule this path is, which is its columns and what each came out as. */
    DecisionRule rule() {
        return rule;
    }
}
