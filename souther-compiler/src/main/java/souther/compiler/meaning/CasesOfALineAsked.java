package souther.compiler.meaning;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;

/**
 * Whether a line decides in some one of the cases a condition was said for, asked a case at a time.
 *
 * <p>A line decides in a case where a row on each side of it can stand in that case: the two rows
 * then differ in the line alone, and the statement turns between them. Asked of the condition the
 * cases were said as, a row on one side may be in one case and the row on the other side in
 * another, and the line turns nothing between those. So the question is asked of each case, and a
 * line decides in the cases said as one only where it decides in one of them.
 *
 * <p><b>Of a case and not of the condition.</b> This is not the question whether rows of a region
 * stand on both sides of a line asked of a region made of several: rows that reach a line along one
 * way or another are one set of rows, and there the question is asked of all of them together. Here
 * what is several is where the statement turns, which is a fact about rows in one case at a time.
 *
 * <p><b>A case is asked part by part as it is chosen.</b> What has been chosen so far holds every
 * row a case chosen further holds, so where it holds no row on one side of the line, neither does
 * any case chosen past it, and those are not asked. A narrower region holds no more rows on either
 * side than a wider one, which is what makes stopping there a proof.
 *
 * <p><b>Counted, and stopped short as a stop.</b> Every question is counted against
 * {@link CompositionBudget#CASES_A_LINE_IS_ASKED_IN} for the one case they were said as, and where
 * the cases were more than were taken apart nothing is asked of them at all. Either way the answer
 * is that it was not worked out, which is neither a case the line turns in nor one it does not.
 *
 * <p>Here, beside where the cases were taken apart, because what a case chosen part by part has
 * chosen so far is a conjunction of the statement's parts, and those are joined where a rule joins
 * them and nowhere else.
 */
public final class CasesOfALineAsked {

    /** What asking found. */
    public sealed interface Found {

        /** Some case holds a row on each side of the line. */
        record InSome() implements Found {}

        /** No case does. */
        record InNone() implements Found {}

        /**
         * Which it is was not worked out, and {@code figures} are every figure some case of them
         * was stopped at: no case was shown to divide rows, and not every case was shown not to.
         */
        record NotWorkedOut(Set<CompositionBudget> figures) implements Found {

            public NotWorkedOut {
                if (figures.isEmpty()) {
                    throw new IllegalArgumentException("what was not worked out stopped at some"
                            + " figure");
                }
                figures = Collections.unmodifiableSet(EnumSet.copyOf(figures));
            }
        }
    }

    private static final Found IN_SOME = new Found.InSome();

    private static final Found IN_NONE = new Found.InNone();

    /** Out of questions: one more is asked than the figure lets be. */
    private static final Found.NotWorkedOut PAST_THE_QUESTIONS =
            new Found.NotWorkedOut(Set.of(CompositionBudget.CASES_A_LINE_IS_ASKED_IN));

    /** The cases were more than were taken apart, and nothing asks them. */
    private static final Found.NotWorkedOut NOT_TAKEN_APART =
            new Found.NotWorkedOut(Set.of(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO));

    private final Predicate<Proposition> crossedIn;

    private int left = CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum();

    /**
     * @param crossedIn whether rows that reach the line with a condition taken in beside the way
     *                  to it stand on each side of it
     */
    public CasesOfALineAsked(Predicate<Proposition> crossedIn) {
        this.crossedIn = crossedIn;
    }

    /**
     * Whether the line decides in some one of the cases {@code said} stands for.
     *
     * <p>Where some one of them holds is asked first, as one question: where it holds no row on
     * one side of the line, neither does any one of them, which settles every case at once. Asked
     * of the cases where they were taken apart, and not of the condition they were said as, which
     * says where some one holds only as far as it was said the same way; where they were not, the
     * condition is all that says it.
     */
    public Found inSomeOf(DecidingCase said) {
        if (!aQuestionIsLeft()) {
            return PAST_THE_QUESTIONS;
        }
        if (!crossedIn.test(said.standsFor().holdingInSome().orElse(said.condition()))) {
            return IN_NONE;
        }
        if (said.saidAlone()) {
            return IN_SOME;
        }
        return chosen(List.of(), List.of(said.standsFor()));
    }

    /**
     * Whether some case holding all of {@code chosen}, and one case of each of {@code toChoose},
     * holds a row on each side of the line — {@code chosen} already shown to.
     */
    private Found chosen(List<Proposition> chosen, List<DecidingCase.Cases> toChoose) {
        if (toChoose.isEmpty()) {
            return IN_SOME;
        }
        List<DecidingCase.Cases> rest = toChoose.subList(1, toChoose.size());
        return switch (toChoose.getFirst()) {
            case DecidingCase.Cases.One(var condition) -> {
                if (!aQuestionIsLeft()) {
                    yield PAST_THE_QUESTIONS;
                }
                List<Proposition> more = new ArrayList<>(chosen);
                more.add(condition);
                yield crossedIn.test(Proposition.all(more)) ? chosen(more, rest) : IN_NONE;
            }
            // Every alternative, and not the first that stopped: one that stopped shows nothing,
            // and another after it may show the line divides rows. Which stopped first decides
            // nothing, so every figure met is said.
            case DecidingCase.Cases.EachOf(var alternatives) -> {
                Set<CompositionBudget> stopped = new HashSet<>();
                boolean shown = false;
                for (DecidingCase.Cases one : alternatives) {
                    List<DecidingCase.Cases> next = new ArrayList<>();
                    next.add(one);
                    next.addAll(rest);
                    Found found = chosen(chosen, next);
                    if (found instanceof Found.InSome) {
                        shown = true;
                        break;
                    }
                    if (found instanceof Found.NotWorkedOut(var figures)) {
                        stopped.addAll(figures);
                    }
                }
                yield shown ? IN_SOME
                        : stopped.isEmpty() ? IN_NONE : new Found.NotWorkedOut(stopped);
            }
            case DecidingCase.Cases.Together(var factors) -> {
                List<DecidingCase.Cases> next = new ArrayList<>(factors);
                next.addAll(rest);
                yield chosen(chosen, next);
            }
            case DecidingCase.Cases.MoreThanWereTakenApart _ -> NOT_TAKEN_APART;
        };
    }

    /** Whether one more question may be asked, counting it where it may. */
    private boolean aQuestionIsLeft() {
        if (left == 0) {
            return false;
        }
        left--;
        return true;
    }
}
