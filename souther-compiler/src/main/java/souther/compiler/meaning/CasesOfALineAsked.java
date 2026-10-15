package souther.compiler.meaning;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.List;
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

        /** Which it is was not worked out, and {@code figure} is what stopped it. */
        record NotWorkedOut(CompositionBudget figure) implements Found {}
    }

    private static final Found IN_SOME = new Found.InSome();

    private static final Found IN_NONE = new Found.InNone();

    private final Predicate<Proposition> crossedIn;

    private int left = CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum();

    /**
     * @param crossedIn whether rows that reach the line with a condition taken in beside the way
     *                  to it stand on each side of it
     */
    public CasesOfALineAsked(Predicate<Proposition> crossedIn) {
        this.crossedIn = crossedIn;
    }

    /** Whether the line decides in some one of {@code cases}. */
    public Found inSomeOf(DecidingCase.Cases cases) {
        return chosen(List.of(), List.of(cases));
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
                if (left == 0) {
                    yield new Found.NotWorkedOut(CompositionBudget.CASES_A_LINE_IS_ASKED_IN);
                }
                left--;
                List<Proposition> more = new ArrayList<>(chosen);
                more.add(condition);
                yield crossedIn.test(Proposition.all(more)) ? chosen(more, rest) : IN_NONE;
            }
            case DecidingCase.Cases.EachOf(var alternatives) -> {
                for (DecidingCase.Cases one : alternatives) {
                    List<DecidingCase.Cases> next = new ArrayList<>();
                    next.add(one);
                    next.addAll(rest);
                    Found found = chosen(chosen, next);
                    if (!(found instanceof Found.InNone)) {
                        yield found;
                    }
                }
                yield IN_NONE;
            }
            case DecidingCase.Cases.Together(var factors) -> {
                List<DecidingCase.Cases> next = new ArrayList<>(factors);
                next.addAll(rest);
                yield chosen(chosen, next);
            }
            case DecidingCase.Cases.MoreThanWereTakenApart _ ->
                    new Found.NotWorkedOut(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO);
        };
    }
}
