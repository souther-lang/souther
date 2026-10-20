package souther.compiler.reading;

import souther.compiler.core.Core;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.ReadMeaning;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * Which evaluation of the comparison that keeps the elements of a container is each element's.
 *
 * <p>Three things are meant by an element's being kept and are kept apart: which element of the
 * container it is, which time round a run evaluates the comparison that keeps it, and which visit a
 * recording holds. The first is the container's order ({@link ReadMeaning.Occurrence}); the third is
 * the evidence's ({@link ControlClaim.Visit}). This is the one place the first is joined to the
 * second, and it joins them only where the join follows from what is known of how the comparison
 * gets evaluated — never because the two happen to be counted the same way.
 *
 * <p><b>What the join rests on.</b> The closure that keeps the elements is applied to every element
 * the container holds, once each, in the order the container holds them
 * ({@link souther.compiler.semantics.HowAClosureIsApplied#TO_EVERY_ELEMENT}), and
 * {@link souther.compiler.check.ElementsWrittenOut} writes the elements out in that order. So where
 * every element is kept by the one comparison of one closure, its evaluation on element {@code i} is
 * the {@code i}th a run makes of it. A run that stops before getting to an element makes no later
 * evaluation, which leaves a claim about it unmet and says nothing wrong.
 *
 * <p><b>Where it does not hold.</b> An element kept by two comparisons has passed the first before
 * the second is evaluated on it, so the second's evaluations are numbered among the elements the
 * first kept: which evaluation is whose depends on how the first came out, and is not decided by the
 * container. That is a limit of this join and not of what a comparison means — the evaluation of an
 * element is determined once the first stage's outcomes are — and is declined rather than guessed,
 * with {@link Why} saying which way it was out of reach.
 */
final class ElementEvaluations {

    private ElementEvaluations() {
    }

    /** What keeps one element, as the join needs it: the comparison read in the names that
     *  element's application hands over, and the way it has to come out to keep the element. */
    record Keeping(Denotation truth, boolean holds) {

        Keeping {
            Objects.requireNonNull(truth, "an element is kept by some comparison");
        }
    }

    /** The joined elements: the one comparison, and for each element, in the container's order,
     *  what keeps it. The {@code i}th is the {@code i}th evaluation. */
    record Joined(Core.Binary comparison, List<Keeping> byElement) {

        Joined {
            byElement = List.copyOf(byElement);
        }
    }

    /** Why the elements could not be joined to evaluations. */
    enum Why {

        /** An element is kept by no truth, so nothing says the comparison was evaluated on it. */
        KEPT_BY_NOTHING,

        /** An element is kept by more than one truth, so which evaluation of a later one is its
         *  depends on how the earlier ones came out. */
        KEPT_BY_SEVERAL,

        /** An element is kept by what is not a truth about it, such as the arm of a choice. */
        KEPT_BY_ANOTHER_KIND,

        /** What keeps an element is not a single comparison. */
        NOT_ONE_COMPARISON,

        /** The elements are not all kept by the one comparison, so they are not one closure
         *  applied to each. */
        NOT_ONE_CLOSURE
    }

    /** Either the join, or the reason there is none. */
    sealed interface Result {

        /** The elements are joined. */
        record Matched(Joined joined) implements Result { }

        /** They are not, for this reason. */
        record Declined(Why why) implements Result { }
    }

    /**
     * The evaluations of the comparison that keeps {@code elements}, element by element.
     *
     * @param elements every element of the container as written, in the order a walk of it meets
     *                 them
     */
    static Result of(List<ReadMeaning.Occurrence> elements) {
        Core.Binary comparison = null;
        List<Keeping> byElement = new ArrayList<>();
        for (ReadMeaning.Occurrence element : elements) {
            List<ReadMeaning.Occurrence.Kept> keptBy = element.keptWhere();
            if (keptBy.isEmpty()) {
                return new Result.Declined(Why.KEPT_BY_NOTHING);
            }
            if (keptBy.size() > 1) {
                return new Result.Declined(Why.KEPT_BY_SEVERAL);
            }
            if (!(keptBy.getFirst() instanceof ReadMeaning.Occurrence.Kept.ATruth(
                    Denotation truth, boolean holds))) {
                return new Result.Declined(Why.KEPT_BY_ANOTHER_KIND);
            }
            if (!(Core.withoutStanding(truth.value()) instanceof Core.Binary written)) {
                return new Result.Declined(Why.NOT_ONE_COMPARISON);
            }
            if (comparison != null && written != comparison) {
                return new Result.Declined(Why.NOT_ONE_CLOSURE);
            }
            comparison = written;
            byElement.add(new Keeping(truth, holds));
        }
        return comparison == null ? new Result.Declined(Why.KEPT_BY_NOTHING)
                : new Result.Matched(new Joined(comparison, byElement));
    }
}
