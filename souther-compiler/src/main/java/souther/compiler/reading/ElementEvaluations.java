package souther.compiler.reading;

import souther.compiler.core.Core;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.ReadMeaning;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.TreeMap;

/**
 * Which evaluation of the comparison that keeps the elements of a container is whose.
 *
 * <p>Three things are meant by an element's being kept and are kept apart: which occurrence of an
 * element the container holds, which application of the comparison's closure kept it, and which
 * visit a recording holds. A flatMap after a filter writes one kept element out as many times as it
 * makes pieces of it, so occurrences are not applications: the closure was applied once to the
 * element and four occurrences are kept by that one application. The second is what
 * {@link ReadMeaning.Occurrence.Kept.ATruth#application} says, written by the walk that applied the
 * closure and never counted back from the list it made; the third is the evidence's
 * ({@link ControlClaim.Visit}). This is the one place the second is joined to the third.
 *
 * <p><b>What the join rests on.</b> The closure that keeps the elements is applied to every element
 * of the container it filters, once each, in the order the container holds them
 * ({@link souther.compiler.semantics.HowAClosureIsApplied#TO_EVERY_ELEMENT}), and the walk numbers
 * its applications in that order. So where no occurrence was kept by anything else first, the
 * {@code i}th application is the {@code i}th evaluation a run makes of the comparison. A run that
 * stops before getting to an element makes no later evaluation, which leaves a claim about it
 * unmet and says nothing wrong.
 *
 * <p><b>Where it does not hold.</b> An occurrence kept by two comparisons has passed the first
 * before the second is evaluated on it, so the second's applications are numbered among the
 * elements the first kept: which evaluation is whose depends on how the first came out. That is a
 * limit of this join and not of what a comparison means — the evaluation is determined once the
 * first stage's outcomes are — and it is declined rather than guessed, with
 * {@link WhyNotJoined} saying which way it was out of reach. A meeting that is declined is still a
 * meeting: its sum is made of decisions this could not name, and the measure says so.
 */
final class ElementEvaluations {

    private ElementEvaluations() {
    }

    /** What keeps the elements one application of the closure was handed: the comparison read in
     *  the names that application hands over, and the way it has to come out to keep them. */
    record Keeping(int evaluation, Denotation truth, boolean holds) {

        Keeping {
            Objects.requireNonNull(truth, "an application is a comparison read somewhere");
            if (evaluation < 0) {
                throw new IllegalArgumentException("evaluations are counted from none");
            }
        }
    }

    /** The joined applications: the one comparison, and for each application that kept an
     *  occurrence, in the order a run makes them, what keeps what it was handed. */
    record Joined(Core.Binary comparison, List<Keeping> byEvaluation) {

        Joined {
            byEvaluation = List.copyOf(byEvaluation);
        }
    }

    /** The join, or that there was nothing to join, or the reason there is none. */
    sealed interface Result {

        /** The occurrences are joined. */
        record Matched(Joined joined) implements Result { }

        /**
         * No occurrence is kept by a comparison of its own: the container holds no decision to
         * join, which is no shortfall. An occurrence kept by nothing among others that are kept is
         * a constant in the sum, and takes no part.
         */
        record NothingToJoin() implements Result { }

        /** There are decisions, and they are not joined, for this reason. */
        record NotJoined(WhyNotJoined why) implements Result { }
    }

    /**
     * The evaluations of the comparison that keeps {@code occurrences}, application by
     * application.
     *
     * @param occurrences every occurrence of the container as written, in the order a walk of it
     *                    meets them
     */
    static Result of(List<ReadMeaning.Occurrence> occurrences) {
        Core.Binary comparison = null;
        WhyNotJoined failed = null;
        boolean aDecisionWasMet = false;
        TreeMap<Integer, Keeping> byEvaluation = new TreeMap<>();
        for (ReadMeaning.Occurrence occurrence : occurrences) {
            List<ReadMeaning.Occurrence.Kept> keptBy = occurrence.keptWhere();
            if (keptBy.isEmpty()) {
                continue;
            }
            // Met wherever something keeps it by a comparison, however many things do: an
            // occurrence kept by two comparisons is a decision this cannot join, not a constant.
            aDecisionWasMet |= keptBy.stream().anyMatch(kept ->
                    kept instanceof ReadMeaning.Occurrence.Kept.ATruth(Denotation truth, var _, var _)
                            && Core.withoutStanding(truth.value()) instanceof Core.Binary);
            if (keptBy.size() > 1) {
                failed = failed == null ? WhyNotJoined.KEPT_BY_SEVERAL : failed;
                continue;
            }
            if (!(keptBy.getFirst() instanceof ReadMeaning.Occurrence.Kept.ATruth(
                    Denotation truth, boolean holds, int application))) {
                failed = failed == null ? WhyNotJoined.KEPT_BY_ANOTHER_KIND : failed;
                continue;
            }
            if (!(Core.withoutStanding(truth.value()) instanceof Core.Binary written)) {
                failed = failed == null ? WhyNotJoined.NOT_ONE_COMPARISON : failed;
                continue;
            }
            if (comparison != null && written != comparison) {
                failed = failed == null ? WhyNotJoined.NOT_ONE_CLOSURE : failed;
                continue;
            }
            comparison = written;
            Keeping already = byEvaluation.putIfAbsent(application,
                    new Keeping(application, truth, holds));
            if (already != null && already.holds() != holds) {
                failed = failed == null ? WhyNotJoined.AN_APPLICATION_SAID_TWO_THINGS : failed;
            }
        }
        // A decision was met only where some occurrence is kept by a comparison. What else is in
        // the container then fails the join, and is said; where none is, there is nothing here
        // that was a decision and nothing to say.
        if (!aDecisionWasMet) {
            return new Result.NothingToJoin();
        }
        return failed != null || comparison == null
                ? new Result.NotJoined(failed == null ? WhyNotJoined.NOT_ONE_COMPARISON : failed)
                : new Result.Matched(new Joined(comparison, new ArrayList<>(byEvaluation.values())));
    }
}
