package souther.compiler.reading;

import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.core.Core;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.ReadMeaning;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Which evaluation of the comparison that decides an element is whose.
 *
 * <p>An element decides a total in two ways, and a total is a function of both: whether it is there
 * ({@code keptWhere}, a filter's comparison on it) and what it is worth (the comparison an
 * {@code if} that its value comes to is on). Each is a comparison evaluated once per application of
 * the closure it stands in, or once where it stands in none. Three things are meant by an element's
 * being decided and are kept apart: which occurrence of an element the container holds, which
 * application of the closure decided it, and which visit a recording holds. A flatMap after a
 * filter writes one kept element out as many times as it makes pieces of it, so occurrences are not
 * applications: the closure was applied once to the element and four occurrences are decided by
 * that one application. The application is what
 * {@link ReadMeaning.Occurrence.Kept.ATruth#application} and {@link ReadMeaning.Occurrence#answered}
 * say, written by the walk that applied the closure and never counted back from the list it made;
 * the visit is the evidence's ({@link ControlClaim.Visit}). This is the one place the application is
 * joined to the visit.
 *
 * <p><b>What the join rests on.</b> A closure is applied to every element of the container it is
 * handed, once each, in the order the container holds them
 * ({@link souther.compiler.semantics.HowAClosureIsApplied#TO_EVERY_ELEMENT}), and the walk numbers
 * its applications in that order. So where no element was dropped before the closure was handed it,
 * the {@code i}th application is the {@code i}th evaluation a run makes of its comparison. A run
 * that stops before getting to an element makes no later evaluation, which leaves a claim about it
 * unmet and says nothing wrong.
 *
 * <p><b>Where it does not hold.</b> An occurrence kept by two comparisons has passed the first
 * before the second is evaluated on it, and a value made after a filter is made of the elements it
 * kept: the applications are numbered among the elements the first kept, so which evaluation is
 * whose depends on how the first came out. A choice found beneath a name was evaluated where the name
 * was written, which may be another closure than the one that answered the value, and its
 * application is not this one's. That is a limit of this join and not of what a comparison means —
 * the evaluation is determined once the first stage's outcomes are — and it is declined rather than
 * guessed. Whether a decision with no number is one it can still be asked of is not answered here:
 * a comparison that is evaluated once needs none, and which evaluations a comparison has is a fact
 * of the tree that runs. The decision is returned without a number and the caller, which has that
 * tree, says. A meeting that is declined is still a meeting: its sum is made of decisions this could
 * not name, and the measure says so.
 */
final class ElementEvaluations {

    private ElementEvaluations() {
    }

    /** The key a decision with no number is filed under, which no application has. */
    private static final int UNNUMBERED = -1;

    /**
     * One comparison evaluated on one application, and the way it has to come out for the
     * occurrence it decides to be what it is: kept, for a filter's, and either way for the choice of
     * a value.
     *
     * @param evaluation which application of its closure this is, where that is also the run's own
     *                   count; empty where this has no number to say
     */
    record Decision(Core.Binary comparison, OptionalInt evaluation, Denotation truth,
                    boolean holds) {

        Decision {
            Objects.requireNonNull(comparison, "a decision is of some comparison");
            Objects.requireNonNull(evaluation, "a decision has a number or none");
            Objects.requireNonNull(truth, "an application is a comparison read somewhere");
        }
    }

    /**
     * The joined decisions, each comparison's in the order a run makes them, and how many elements
     * are kept, as a count of them is made of.
     *
     * <p>A total takes no part of an element nothing varies, and a count does: the number kept is
     * what is kept whatever a row chooses, plus the weight of each decision that keeps. So a count
     * is no function of the decisions alone, and a reader that took it for one would count a fixed
     * element as none and several elements one decision keeps as one.
     *
     * @param weights how many occurrences each decision keeps, one for each, in the same order; none
     *                for a decision that decides what an occurrence is worth
     * @param fixed   how many occurrences are kept whatever a row chooses, or empty where that is not
     *                known: a count of what a test that is the same on every run keeps is not worked
     *                out here, since which way that test comes out is not
     */
    record Joined(List<Decision> decisions, List<Integer> weights, OptionalInt fixed) {

        Joined {
            decisions = List.copyOf(decisions);
            weights = List.copyOf(weights);
            Objects.requireNonNull(fixed, "a count has a base or none that is known");
        }
    }

    /** What the occurrences nothing varies come to, as the base of a count. */
    private static final class Fixed {

        private int kept;
        private boolean known = true;

        OptionalInt asKnown() {
            return known ? OptionalInt.of(kept) : OptionalInt.empty();
        }
    }

    /** The join, or that there was nothing to join, or the reason there is none. */
    sealed interface Result {

        /** The occurrences are joined. */
        record Matched(Joined joined) implements Result { }

        /**
         * Nothing decides any occurrence that matters: the container holds no decision to join,
         * which is no shortfall. An occurrence decided by nothing among others that are is a
         * constant in the sum, and takes no part.
         */
        record NothingToJoin() implements Result { }

        /** There are decisions, and they are not joined, for this reason. */
        record NotJoined(WhyNotJoined why) implements Result { }
    }

    /**
     * The evaluations of the comparisons that decide {@code occurrences}, application by
     * application.
     *
     * @param occurrences  every occurrence of the container as written, in the order a walk of it
     *                     meets them
     * @param contributes  whether an occurrence can change the answer: an element worth what an empty
     *                     total is worth does not, kept or not, and its decisions are none of the
     *                     answer's
     * @param valueMatters whether what an occurrence is worth decides the answer: it does for a total
     *                     and does not for a count, which is the same however the values come out
     * @param statementsCountIt whether the answer is a count that a comparison is made of, which
     *                     the reading of statements takes up: what it counts is the statements that
     *                     hold, and an element kept by what a quantifier states is one of them
     * @param folded       the constant a truth comes to on every run, where it comes to one
     * @param sameOnEveryRun whether a truth is made of what is written and nothing a run is handed,
     *                     so that it comes out the same on every run whether or not it folds. Nothing
     *                     a row chooses varies it, so it is no decision; which way it comes out is
     *                     not worked out, so whether an occurrence it keeps is there is not known,
     *                     which a count of them says ({@link Joined#fixed}) and a join of what else
     *                     keeps that occurrence declines
     * @param choicesOf    what decides the value of an occurrence
     */
    static Result of(List<ReadMeaning.Occurrence> occurrences,
                     Predicate<ReadMeaning.Occurrence> contributes, boolean valueMatters,
                     boolean statementsCountIt,
                     Function<Denotation, Optional<Object>> folded,
                     Predicate<Denotation> sameOnEveryRun,
                     Function<Denotation, ValueChoices.Of> choicesOf) {
        List<Deciding> deciding = new ArrayList<>();
        Fixed base = new Fixed();
        for (ReadMeaning.Occurrence occurrence : occurrences) {
            if (contributes.test(occurrence)) {
                Deciding each = decidingOf(occurrence, valueMatters, statementsCountIt, folded,
                        sameOnEveryRun, choicesOf, base);
                if (each != null) {
                    deciding.add(each);
                }
            }
        }
        // What a meeting is of is decisions that are not one another's, and that is settled before
        // anything is read of them: a single one meets nothing, whether or not it could be read,
        // and an occurrence nothing varies is no decision. Where there are two or more and this
        // cannot join them, that is said: a decision this reading has no words for is still one.
        if (apartIn(deciding) < 2) {
            return new Result.NothingToJoin();
        }
        Map<Core.Binary, Map<Integer, Decision>> byComparison = new IdentityHashMap<>();
        List<Core.Binary> inTheOrderMet = new ArrayList<>();
        Core.Binary keeping = null;
        Core.Binary valuing = null;
        WhyNotJoined failed = null;
        Map<Decision, Integer> weights = new IdentityHashMap<>();
        for (Deciding one : deciding) {
            ReadMeaning.Occurrence occurrence = one.occurrence();
            List<ReadMeaning.Occurrence.Kept> keptBy = one.keptBy();
            if (!keptBy.isEmpty()) {
                // Kept by a test the same on every run beside what varies it: whether it is there
                // at all is not worked out, and a decision of an element that may not be is no
                // decision to ask a row for.
                WhyNotJoined why = keptBy.size() > 1 || one.unsure()
                        ? WhyNotJoined.KEPT_BY_SEVERAL : null;
                if (why == null && keptBy.getFirst() instanceof ReadMeaning.Occurrence.Kept.ATruth(
                        Denotation truth, boolean holds, OptionalInt application)) {
                    // A conjunction is an operator and stands as a Binary, and is not one
                    // comparison: which of its parts came out which way is not which way it did.
                    if (!(Core.withoutStanding(truth.value()) instanceof Core.Binary written)
                            || written.op().stopsWhenItsAnswerIsSettled()) {
                        why = WhyNotJoined.NOT_ONE_COMPARISON;
                    } else if (keeping != null && written != keeping) {
                        why = WhyNotJoined.NOT_ONE_CLOSURE;
                    } else {
                        keeping = written;
                        Decision filed = put(byComparison, inTheOrderMet, new Decision(written,
                                application, truth, holds));
                        if (filed.holds() != holds) {
                            why = WhyNotJoined.AN_APPLICATION_SAID_TWO_THINGS;
                        } else {
                            weights.merge(filed, 1, Integer::sum);
                        }
                    }
                } else if (why == null) {
                    why = WhyNotJoined.KEPT_BY_ANOTHER_KIND;
                }
                failed = failed == null ? why : failed;
            }
            if (one.choice() != null) {
                switch (one.choice()) {
                    case ValueChoices.Of.Fixed _ -> { }
                    case ValueChoices.Of.Unread _ ->
                        failed = failed == null ? WhyNotJoined.A_VALUE_CHOICE_NOT_READ : failed;
                    case ValueChoices.Of.OneComparison(Core.Binary comparison, var at,
                                                       boolean viaNames, boolean _) -> {
                        // The number the walk gave the application is this comparison's only
                        // where the comparison is the closure's own. Found beneath a name it was
                        // evaluated where the name was written, which is another closure's
                        // application or none; and an element no closure made was written where
                        // it stands and has none.
                        OptionalInt number = viaNames ? OptionalInt.empty()
                                : occurrence.answered();
                        // Two comparisons that are closures' own are two closures, which is not
                        // one application of each. One that has no number says nothing of which
                        // closure it is in.
                        if (number.isPresent() && valuing != null && comparison != valuing) {
                            failed = failed == null ? WhyNotJoined.NOT_ONE_CLOSURE : failed;
                        } else {
                            valuing = number.isPresent() ? comparison : valuing;
                            put(byComparison, inTheOrderMet, new Decision(comparison, number,
                                    new Denotation(comparison, at), true));
                        }
                    }
                }
            }
        }
        if (failed != null) {
            return new Result.NotJoined(failed);
        }
        List<Decision> decisions = new ArrayList<>();
        for (Core.Binary comparison : inTheOrderMet) {
            byComparison.get(comparison).values().stream()
                    .sorted(Comparator.comparingInt(each -> each.evaluation().orElse(UNNUMBERED)))
                    .forEach(decisions::add);
        }
        return decisions.isEmpty() ? new Result.NotJoined(WhyNotJoined.NOT_ONE_COMPARISON)
                : new Result.Matched(new Joined(decisions,
                        decisions.stream().map(each -> weights.getOrDefault(each, 0)).toList(),
                        base.asKnown()));
    }

    /** An occurrence that something varies: what keeps it, once what is settled is set aside, and
     *  what decides its worth, where that matters. Whether it is there at all is not known where a
     *  test that is the same on every run also keeps it ({@code unsure}). */
    private record Deciding(ReadMeaning.Occurrence occurrence,
                            List<ReadMeaning.Occurrence.Kept> keptBy, ValueChoices.Of choice,
                            boolean unsure) { }

    /**
     * Which evaluation of {@code fork} decides {@code occurrence}, or null where that is not
     * something this knows. Two occurrences decided by the same evaluation of the same fork are
     * decided by one decision, however many times the value is used or what is done with it.
     *
     * <p>A fork is evaluated once for each application of each closure it is written in, and by
     * nothing else: not by what is done with its result, nor by what else is written in the
     * closures the result passes through. One the closure of the occurrence's own step writes is
     * told by that step's application. One held in a name is told by the applications that wrote
     * the occurrence out, of those closures that hold it. Where it is written in an application
     * no step that wrote the occurrence out accounts for, which application it is is not known.
     */
    private static Object evaluatedAs(Core fork, boolean viaNames, boolean perApplication,
                                      ReadMeaning.Occurrence occurrence) {
        if (!viaNames) {
            return occurrence.answered().isPresent() ? (Object) occurrence.answered().getAsInt()
                    : null;
        }
        List<Integer> evaluated = new ArrayList<>();
        for (ElementsWrittenOut.Applied applied : occurrence.within()) {
            if (writes(applied.body(), fork)) {
                evaluated.add(applied.application());
            }
        }
        return perApplication && evaluated.isEmpty() ? null : evaluated;
    }

    /** Whether {@code target}, which is not a copy, is written anywhere in {@code within}. */
    private static boolean writes(Core within, Core target) {
        if (Core.withoutStanding(within) == target) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(within, child -> found[0] = found[0] || writes(child, target));
        return found[0];
    }

    /**
     * {@code occurrence} as what varies it, or null where nothing does.
     *
     * <p>Nothing varies an occurrence that a constant keeps in, or keeps out: an element a filter
     * keeps whatever the run is the same element written without the filter, and one it never
     * keeps is not in the list at all. Nor one the reading of statements takes up, or one whose
     * worth is fixed and that nothing else keeps out.
     */
    private static Deciding decidingOf(ReadMeaning.Occurrence occurrence, boolean valueMatters,
                                       boolean statementsCountIt,
                                       Function<Denotation, Optional<Object>> folded,
                                       Predicate<Denotation> sameOnEveryRun,
                                       Function<Denotation, ValueChoices.Of> choicesOf,
                                       Fixed base) {
        List<ReadMeaning.Occurrence.Kept> keptBy = new ArrayList<>();
        // Whether a test kept it by that is the same on every run, of which the answer is not worked
        // out: it is kept on every run or on none, and which is not known.
        boolean unsure = false;
        for (ReadMeaning.Occurrence.Kept kept : occurrence.keptWhere()) {
            if (kept instanceof ReadMeaning.Occurrence.Kept.ATruth(Denotation truth, boolean holds,
                                                                   OptionalInt _)) {
                if (folded.apply(truth).orElse(null) instanceof Boolean settled) {
                    if (settled != holds) {
                        return null;
                    }
                    continue;
                }
                // The same on every run, so nothing a row chooses.
                if (sameOnEveryRun.test(truth)) {
                    unsure = true;
                    continue;
                }
            }
            keptBy.add(kept);
        }
        base.known &= !unsure;
        if (statementsCountIt && isKeptByAQuantifierHolding(keptBy)) {
            // How many are kept, where each is kept by what a quantifier states of a container
            // and the count is compared, is the count of statements that hold. That is read as
            // the statements are, and says itself when it cannot be.
            base.known = false;
            return null;
        }
        ValueChoices.Of choice = valueMatters ? choicesOf.apply(occurrence.value()) : null;
        if (keptBy.isEmpty() && (choice == null || choice instanceof ValueChoices.Of.Fixed)) {
            base.kept++;
            return null;
        }
        return new Deciding(occurrence, keptBy, choice, unsure);
    }

    /**
     * How many decisions there are that are not one another's.
     *
     * <p>A decision is told by what it is made of and the application of it: the one comparison a
     * filter evaluates for each element is as many decisions as it has applications, an element
     * written out twice is one, and a choice made once and named is one however often the name is
     * used. Where what an occurrence is decided by cannot be placed that way, it is counted as its
     * own, so that a count never falls short of the decisions there are.
     */
    private static int apartIn(List<Deciding> deciding) {
        // Each decision's made-ness: the application that made it, the writing out it was made
        // in, or once.
        Map<Core, Set<Object>> placed = new IdentityHashMap<>();
        int unplaced = 0;
        for (Deciding one : deciding) {
            for (ReadMeaning.Occurrence.Kept kept : one.keptBy()) {
                if (kept instanceof ReadMeaning.Occurrence.Kept.ATruth(Denotation truth, boolean _,
                                                                       OptionalInt application)
                        && application.isPresent()) {
                    placed.computeIfAbsent(Core.withoutStanding(truth.value()),
                            _ -> new HashSet<>()).add(application.getAsInt());
                } else if (kept instanceof ReadMeaning.Occurrence.Kept.AnArm(Denotation fork, int _)
                        && evaluatedOnce(one.occurrence())) {
                    // The arms of one fork, read in one reading, are outcomes of one evaluation:
                    // a run takes one of them, and the elements they write are not decided apart.
                    placed.computeIfAbsent(Core.withoutStanding(fork.value()),
                            _ -> new HashSet<>()).add(new OneReading(fork.at()));
                } else {
                    unplaced++;
                }
            }
            switch (one.choice()) {
                case null -> { }
                case ValueChoices.Of.Fixed _ -> { }
                case ValueChoices.Of.Unread(List<ValueChoices.Origin> origins) -> {
                    // A value decided by several choices has each of them, and a walk that gave
                    // up before it found them all may have left two where it names one.
                    for (ValueChoices.Origin each : origins) {
                        if (each.fork() == null) {
                            unplaced += 2;
                        } else {
                            Object made = evaluatedAs(each.fork(), each.viaNames(),
                                    each.perApplication(), one.occurrence());
                            if (made == null) {
                                unplaced++;
                            } else {
                                placed.computeIfAbsent(each.fork(), _ -> new HashSet<>()).add(made);
                            }
                        }
                    }
                }
                case ValueChoices.Of.OneComparison(Core.Binary comparison, var _,
                                                   boolean viaNames, boolean perApplication) -> {
                    Object made = evaluatedAs(comparison, viaNames, perApplication,
                            one.occurrence());
                    if (made == null) {
                        unplaced++;
                    } else {
                        placed.computeIfAbsent(comparison, _ -> new HashSet<>()).add(made);
                    }
                }
            }
        }
        return unplaced + placed.values().stream().mapToInt(Set::size).sum();
    }

    /** One reading of a fork, told from another by being another object: a reading's own equality
     *  compares what it holds, and two readings of one fork that hold alike are still two. */
    private record OneReading(Object reading) {

        @Override
        public boolean equals(Object other) {
            return other instanceof OneReading one && one.reading == reading;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(reading);
        }
    }

    /** Whether no application of any closure wrote {@code occurrence} out, so that a fork it was
     *  kept by is evaluated once for each reading of it and not once for each application. */
    private static boolean evaluatedOnce(ReadMeaning.Occurrence occurrence) {
        return occurrence.answered().isEmpty() && occurrence.within().isEmpty();
    }

    /** Whether the one thing that keeps an occurrence is a quantifier ({@code all}, {@code any})
     *  that came out true, which is what the reading of statements states of its container. One
     *  that came out false states no element, and is no statement. */
    private static boolean isKeptByAQuantifierHolding(List<ReadMeaning.Occurrence.Kept> keptBy) {
        return keptBy.size() == 1
                && keptBy.getFirst() instanceof ReadMeaning.Occurrence.Kept.ATruth truth
                && truth.holds()
                && Core.withoutStanding(truth.truth().value()) instanceof Core.PreservedCall call
                && DefaultBoundOperationFacts.get().statesItsPredicateOfEveryElement(
                        call.operation());
    }

    /** The decision filed under {@code decision}'s comparison and application: it, or the one
     *  already there. */
    private static Decision put(Map<Core.Binary, Map<Integer, Decision>> byComparison,
                                List<Core.Binary> inTheOrderMet, Decision decision) {
        Map<Integer, Decision> filed = byComparison.get(decision.comparison());
        if (filed == null) {
            filed = new TreeMap<>();
            byComparison.put(decision.comparison(), filed);
            inTheOrderMet.add(decision.comparison());
        }
        return filed.computeIfAbsent(decision.evaluation().orElse(UNNUMBERED), _ -> decision);
    }
}
