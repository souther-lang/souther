package souther.compiler.reading;

import souther.compiler.core.Core;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.ReadMeaning;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.OptionalInt;
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

    /** The joined decisions, each comparison's in the order a run makes them. */
    record Joined(List<Decision> decisions) {

        Joined {
            decisions = List.copyOf(decisions);
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
     * @param choicesOf    what decides the value of an occurrence
     */
    static Result of(List<ReadMeaning.Occurrence> occurrences,
                     Predicate<ReadMeaning.Occurrence> contributes, boolean valueMatters,
                     Function<Denotation, ValueChoices.Of> choicesOf) {
        Map<Core.Binary, Map<Integer, Decision>> byComparison = new IdentityHashMap<>();
        List<Core.Binary> inTheOrderMet = new ArrayList<>();
        Core.Binary keeping = null;
        Core.Binary valuing = null;
        WhyNotJoined failed = null;
        boolean aDecisionWasMet = false;
        for (ReadMeaning.Occurrence occurrence : occurrences) {
            if (!contributes.test(occurrence)) {
                continue;
            }
            List<ReadMeaning.Occurrence.Kept> keptBy = occurrence.keptWhere();
            if (!valueMatters && isKeptByAStatementOverAContainer(keptBy)) {
                // How many are kept, where each is kept by what a quantifier states of a
                // container, is the count of statements that hold, and that is read as the
                // statements are, with the reasons it cannot be that reading says itself. It is no
                // evaluation of one comparison to join, and is not left unread here.
                continue;
            }
            if (!keptBy.isEmpty()) {
                // Met wherever anything keeps an occurrence, whatever it is and however many things
                // do. That a decision exists is a fact about the container; whether this reading
                // can place it is a fact about this reading, and is said below when it cannot.
                aDecisionWasMet = true;
                WhyNotJoined why = keptBy.size() > 1 ? WhyNotJoined.KEPT_BY_SEVERAL : null;
                if (why == null && keptBy.getFirst() instanceof ReadMeaning.Occurrence.Kept.ATruth(
                        Denotation truth, boolean holds, int application)) {
                    // A conjunction is an operator and stands as a Binary, and is not one
                    // comparison: which of its parts came out which way is not which way it did.
                    if (!(Core.withoutStanding(truth.value()) instanceof Core.Binary written)
                            || written.op().stopsWhenItsAnswerIsSettled()) {
                        why = WhyNotJoined.NOT_ONE_COMPARISON;
                    } else if (keeping != null && written != keeping) {
                        why = WhyNotJoined.NOT_ONE_CLOSURE;
                    } else {
                        keeping = written;
                        Decision already = put(byComparison, inTheOrderMet, new Decision(written,
                                OptionalInt.of(application), truth, holds));
                        if (already != null && already.holds() != holds) {
                            why = WhyNotJoined.AN_APPLICATION_SAID_TWO_THINGS;
                        }
                    }
                } else if (why == null) {
                    why = WhyNotJoined.KEPT_BY_ANOTHER_KIND;
                }
                failed = failed == null ? why : failed;
            }
            if (valueMatters) {
                switch (choicesOf.apply(occurrence.value())) {
                    case ValueChoices.Of.Fixed _ -> { }
                    case ValueChoices.Of.Unread _ -> {
                        aDecisionWasMet = true;
                        failed = failed == null ? WhyNotJoined.A_VALUE_CHOICE_NOT_READ : failed;
                    }
                    case ValueChoices.Of.OneComparison(Core.Binary comparison, var at,
                                                       boolean viaNames) -> {
                        aDecisionWasMet = true;
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
        // Where nothing decides any occurrence there is no decision and nothing to say. Where
        // something does, and this could not join it, that is said: a decision this reading has no
        // words for is still one.
        if (!aDecisionWasMet) {
            return new Result.NothingToJoin();
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
                : new Result.Matched(new Joined(decisions));
    }

    /** Whether the one thing that keeps an occurrence is a truth that is not an operator's: a call
     *  such as {@code all} or {@code any} over a container, or a match. */
    private static boolean isKeptByAStatementOverAContainer(
            List<ReadMeaning.Occurrence.Kept> keptBy) {
        return keptBy.size() == 1
                && keptBy.getFirst() instanceof ReadMeaning.Occurrence.Kept.ATruth truth
                && !(Core.withoutStanding(truth.truth().value()) instanceof Core.Binary);
    }

    /** {@code decision} filed under its comparison and application, or the one already there. */
    private static Decision put(Map<Core.Binary, Map<Integer, Decision>> byComparison,
                                List<Core.Binary> inTheOrderMet, Decision decision) {
        Map<Integer, Decision> filed = byComparison.get(decision.comparison());
        if (filed == null) {
            filed = new TreeMap<>();
            byComparison.put(decision.comparison(), filed);
            inTheOrderMet.add(decision.comparison());
        }
        return filed.putIfAbsent(decision.evaluation().orElse(UNNUMBERED), decision);
    }
}
