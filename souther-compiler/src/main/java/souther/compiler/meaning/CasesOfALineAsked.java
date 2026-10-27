package souther.compiler.meaning;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Which of the cases a condition was said for a line decides in, asked a case at a time.
 *
 * <p>A line decides in a case where a row on each side of it can stand in that case: the two rows
 * then differ in the line alone, and the statement turns between them. Asked of the condition the
 * cases were said as, a row on one side may be in one case and the row on the other side in
 * another, and the line turns nothing between those. So the question is asked of each case, and a
 * line decides in the cases said as one only where it decides in one of them.
 *
 * <p><b>Which cases, and not whether some.</b> A row meets the line only in a case the line turns
 * in. A case the line turns nothing in can still hold one of its points, on the one side its rows
 * are on, and a row there says nothing about the line; kept under the condition said for all of
 * them, it would be counted for the point. So every case is asked, and the ones that divide rows
 * are what the line is read in.
 *
 * <p><b>Of a case and not of the condition.</b> This is not the question whether rows of a region
 * stand on both sides of a line asked of a region made of several: rows that reach a line along one
 * way or another are one set of rows, and there the question is asked of all of them together. Here
 * what is several is where the statement turns, which is a fact about rows in one case at a time.
 *
 * <p><b>A case is asked part by part as it is chosen.</b> What has been chosen so far holds every
 * row a case chosen further holds, so where it holds no row on one side of the line, neither does
 * any case chosen past it, and those are not asked. A narrower region holds no more rows on either
 * side than a wider one, which is what makes stopping there a proof. The converse is not one: rows
 * on both sides of what has been chosen so far may each be in a case of their own further on, so a
 * case is one the line decides in only once it is chosen to the end.
 *
 * <p><b>As many cases as are taken apart, and no more.</b> How many ways there are of choosing a
 * case is counted off the choices before any is asked ({@link DecidingCase.Cases#waysOfChoosing}),
 * and past {@link CompositionBudget#CASES_A_LINE_IS_TAKEN_APART_INTO} none is asked: those are
 * more cases than are taken apart, whether they were written out or said as choices, and the line
 * is not worked out in them at that figure.
 *
 * <p><b>Counted by the step, and stopped short as a stop.</b> Every step of the choosing is counted
 * against {@link CompositionBudget#CASES_A_LINE_IS_ASKED_IN} for the one case they were said as:
 * each alternative taken and each part asked. Counted by the questions alone, the alternatives
 * would be walked unbounded where nothing is asked — the cases of a choice nobody took apart, or
 * every way of choosing past the last question allowed — and those are as many as the product of
 * the choices. Where the steps run out the choosing stops there, and says the figures it met and,
 * of what it did not walk to, only what is written in the cases already: that some were never
 * taken apart, and the figure each stopped at. And where the cases were never taken apart nothing
 * is asked of them at all. Either way what was not walked is neither a case the line turns in nor
 * one it does not, and the cases already shown to divide rows are what they are beside it.
 *
 * <p>Here, beside where the cases were taken apart, because what a case chosen part by part has
 * chosen so far is a conjunction of the statement's parts, and those are joined where a rule joins
 * them and nowhere else.
 */
public final class CasesOfALineAsked {

    /**
     * What asking found.
     *
     * @param decidesIn  the cases shown to hold a row on each side of the line, each by itself; the
     *                   case asked, as it was said, where every case it stands for is one of them.
     *                   How many of them a line is read in one by one is the line's to say, over
     *                   every case it holds ({@link DecidingCase#saidInAsFewAsMay})
     * @param notWorkedOut every figure some case was stopped at, where some was: which way those
     *                   cases go was not worked out, and empty where every case was
     */
    public record Found(List<DecidingCase> decidesIn, Set<CompositionBudget> notWorkedOut) {

        public Found {
            decidesIn = DecidingCase.eachByItsOwnCondition(decidesIn);
            notWorkedOut = notWorkedOut.isEmpty() ? Set.of()
                    : Collections.unmodifiableSet(EnumSet.copyOf(notWorkedOut));
        }
    }

    private static final Found IN_NONE = new Found(List.of(), Set.of());

    private final Predicate<Proposition> crossedIn;

    private int left = CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum();

    /** Each case shown to divide rows, as the conjunction of what it chose. */
    private final Set<Proposition> dividing = new LinkedHashSet<>();

    /** Whether some case was shown to divide no rows. */
    private boolean dropped;

    private final Set<CompositionBudget> stopped = EnumSet.noneOf(CompositionBudget.class);

    private CasesOfALineAsked(Predicate<Proposition> crossedIn) {
        this.crossedIn = crossedIn;
    }

    /**
     * Which of the cases {@code said} stands for the line decides in.
     *
     * <p>Where some one of them holds is asked first, as one question: where it holds no row on
     * one side of the line, neither does any one of them, which settles every case at once. Asked
     * of the cases where they were taken apart, and not of the condition they were said as, which
     * says where some one holds only as far as it was said the same way; where they were not, the
     * condition is all that says it.
     *
     * @param crossedIn whether rows that reach the line with a condition taken in beside the way
     *                  to it stand on each side of it
     */
    public static Found casesOf(DecidingCase said, Predicate<Proposition> crossedIn) {
        return new CasesOfALineAsked(crossedIn).asked(said);
    }

    /**
     * One case taken apart to the end, and what asking it came to.
     *
     * @param condition the conjunction of what the case chose
     * @param answer    what was asked of that condition
     */
    public record Atom<T>(Proposition condition, T answer) {

        public Atom {
            Objects.requireNonNull(condition, "a case is some condition");
        }
    }

    /**
     * What asking found of every case a condition was said for.
     *
     * @param each         every case taken apart to the end that was walked to, in the order they
     *                     are chosen, each with its answer
     * @param notWorkedOut every figure some case was stopped at, where some was: those cases are
     *                     in none of {@code each}, and empty where every case was walked to
     */
    public record Atoms<T>(List<Atom<T>> each, Set<CompositionBudget> notWorkedOut) {

        public Atoms {
            each = List.copyOf(each);
            notWorkedOut = notWorkedOut.isEmpty() ? Set.of()
                    : Collections.unmodifiableSet(EnumSet.copyOf(notWorkedOut));
        }
    }

    /**
     * What {@code answer} comes to in each of the cases {@code said} stands for, each asked by
     * itself and none given up on the strength of another.
     *
     * <p>For an answer that is not about one line fixed beforehand: what parts the values a
     * relation settles is read off the rows in a case, and a narrower case can part values that a
     * wider one does not. Nothing is kept or dropped here, so nothing hangs on the answers being
     * the same for a case and for the cases it is part of; it is the caller's to say which of the
     * answers it keeps, and to say each case it kept none of. The steps and the ways of choosing
     * are counted as they are for {@link #casesOf}.
     */
    public static <T> Atoms<T> atomsOf(DecidingCase said, Function<Proposition, T> answer) {
        return new CasesOfALineAsked(_ -> true).allAsked(said, answer);
    }

    private <T> Atoms<T> allAsked(DecidingCase said, Function<Proposition, T> answer) {
        if (!aStepIsLeft()) {
            pastTheSteps(List.of(said.standsFor()));
            return new Atoms<>(List.of(), stopped);
        }
        if (said.saidAlone()) {
            return new Atoms<>(List.of(new Atom<>(said.condition(), answer.apply(said.condition()))),
                    Set.of());
        }
        long most = CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum();
        if (said.standsFor().waysOfChoosing(most) > most) {
            stopped.add(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO);
            notTakenApartAt(said.standsFor(), stopped);
            return new Atoms<>(List.of(), stopped);
        }
        List<Atom<T>> out = new ArrayList<>();
        chosen(new ArrayList<>(), List.of(heldFirst(said.standsFor())), _ -> true,
                chosen -> out.add(new Atom<>(chosen, answer.apply(chosen))));
        return new Atoms<>(out, stopped);
    }

    private Found asked(DecidingCase said) {
        if (!aStepIsLeft()) {
            pastTheSteps(List.of(said.standsFor()));
            return new Found(List.of(), stopped);
        }
        // Said as choices, the cases of a line that decides in more ways than are written out are
        // as many as their product, and the condition holding in some one of them would be as long
        // as they are many. They are not asked as one condition then, but by the condition they
        // were said as, which holds exactly where one of them does; and they are not all asked,
        // since a prefix with no row on one side of the line leaves every case past it unasked,
        // and the steps bound the rest.
        long most = CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum();
        boolean writtenOut = said.standsFor().waysOfChoosing(most) <= most;
        if (!crossedIn.test(writtenOut
                ? said.standsFor().holdingInSome().orElse(said.condition())
                : said.condition())) {
            return IN_NONE;
        }
        if (said.saidAlone()) {
            return new Found(List.of(said), Set.of());
        }
        chosen(new ArrayList<>(), List.of(heldFirst(said.standsFor())), crossedIn,
                chosen -> dividing.add(chosen));
        // Every case divides rows and every one was worked out: the case is what it was said as,
        // and saying it again would read the line under another condition for nothing.
        if (!dropped && stopped.isEmpty() && !dividing.isEmpty()) {
            return new Found(List.of(said), Set.of());
        }
        return new Found(dividing.stream().map(DecidingCase::alone).toList(), stopped);
    }

    /**
     * {@code cases} with what every case of them holds written before the choices, at every depth
     * choosing together is written to.
     *
     * <p>A prefix is walked further only while rows stand on both sides of the line in it, and what
     * is certain to be chosen narrows it from the first alternative on. Chosen last, the parts
     * every case holds are asked once for each way of choosing, and the ones that contradict them
     * are found only at the end of each.
     *
     * <p>Choosing together is associative, so a group written inside a group is the parts of both.
     * What is written under an alternative is held only where the alternative is taken, and stays
     * in it: each alternative is put in this order on its own. The choices keep the order they
     * were written in, since a choice nobody took apart ends the walk there.
     */
    private static DecidingCase.Cases heldFirst(DecidingCase.Cases cases) {
        return heldFirst(cases, new IdentityHashMap<>());
    }

    /** The same, where the cases share what follows from a choice: each is put in order once. */
    private static DecidingCase.Cases heldFirst(DecidingCase.Cases cases,
                                                Map<DecidingCase.Cases, DecidingCase.Cases> done) {
        DecidingCase.Cases known = done.get(cases);
        if (known != null) {
            return known;
        }
        DecidingCase.Cases ordered = switch (cases) {
            case DecidingCase.Cases.One _, DecidingCase.Cases.NotTakenApart _ -> cases;
            case DecidingCase.Cases.EachOf(var alternatives) -> new DecidingCase.Cases.EachOf(
                    alternatives.stream().map(one -> heldFirst(one, done)).toList());
            case DecidingCase.Cases.Together(var factors) -> {
                List<DecidingCase.Cases> held = new ArrayList<>();
                List<DecidingCase.Cases> choices = new ArrayList<>();
                gatherHeldFirst(factors, held, choices, done);
                held.addAll(choices);
                yield new DecidingCase.Cases.Together(held);
            }
        };
        done.put(cases, ordered);
        return ordered;
    }

    private static void gatherHeldFirst(List<DecidingCase.Cases> factors,
                                        List<DecidingCase.Cases> held,
                                        List<DecidingCase.Cases> choices,
                                        Map<DecidingCase.Cases, DecidingCase.Cases> done) {
        for (DecidingCase.Cases factor : factors) {
            switch (factor) {
                case DecidingCase.Cases.One _ -> held.add(factor);
                case DecidingCase.Cases.Together(var inner) ->
                        gatherHeldFirst(inner, held, choices, done);
                case DecidingCase.Cases.EachOf _, DecidingCase.Cases.NotTakenApart _ ->
                        choices.add(heldFirst(factor, done));
            }
        }
    }

    /**
     * Each case holding all of {@code chosen}, and one case of each of {@code toChoose}, that holds
     * a row on each side of the line — {@code chosen} already shown to.
     *
     * <p>{@code chosen} is the one path walked, taken a part further on the way down and given back
     * on the way up, and written out only for a case kept. {@code goesOn} says whether what has
     * been chosen so far is walked further, and {@code atEnd} takes each case chosen to the end.
     */
    private void chosen(List<Proposition> chosen, List<DecidingCase.Cases> toChoose,
                        Predicate<Proposition> goesOn, Consumer<Proposition> atEnd) {
        if (toChoose.isEmpty()) {
            atEnd.accept(Proposition.all(chosen));
            return;
        }
        List<DecidingCase.Cases> rest = toChoose.subList(1, toChoose.size());
        switch (toChoose.getFirst()) {
            case DecidingCase.Cases.One(var condition) -> {
                if (!aStepIsLeft()) {
                    pastTheSteps(toChoose);
                    return;
                }
                chosen.add(condition);
                if (goesOn.test(Proposition.all(chosen))) {
                    chosen(chosen, rest, goesOn, atEnd);
                } else {
                    dropped = true;
                }
                chosen.removeLast();
            }
            // Every alternative: one that divides rows is no answer about another. Each taken is
            // a step, and where the steps run out the ones not taken are not walked.
            case DecidingCase.Cases.EachOf(var alternatives) -> {
                for (int at = 0; at < alternatives.size(); at++) {
                    if (!aStepIsLeft()) {
                        List<DecidingCase.Cases> notWalked =
                                new ArrayList<>(alternatives.subList(at, alternatives.size()));
                        notWalked.addAll(rest);
                        pastTheSteps(notWalked);
                        return;
                    }
                    List<DecidingCase.Cases> next = new ArrayList<>();
                    next.add(alternatives.get(at));
                    next.addAll(rest);
                    chosen(chosen, next, goesOn, atEnd);
                }
            }
            case DecidingCase.Cases.Together(var factors) -> {
                List<DecidingCase.Cases> next = new ArrayList<>(factors);
                next.addAll(rest);
                chosen(chosen, next, goesOn, atEnd);
            }
            // Nobody took them apart, and nothing asks them.
            case DecidingCase.Cases.NotTakenApart(var stoppedAt) -> stopped.add(stoppedAt);
        }
    }

    /**
     * Out of steps, with {@code notWalked} left: stopped at the steps, and at each figure a case
     * left was stopped at where it was never taken apart.
     *
     * <p>The others are not work this would have done. That the cases were never taken apart was
     * met where they were taken apart, and is written in the cases themselves, so it is read off
     * them as they stand — once over each, and not by choosing among them.
     */
    private void pastTheSteps(List<DecidingCase.Cases> notWalked) {
        stopped.add(CompositionBudget.CASES_A_LINE_IS_ASKED_IN);
        notWalked.forEach(each -> notTakenApartAt(each, stopped));
    }

    /** Adds to {@code figures} each figure a case {@code cases} stands for was stopped at, where
     *  it was never taken apart. */
    private static void notTakenApartAt(DecidingCase.Cases cases, Set<CompositionBudget> figures) {
        switch (cases) {
            case DecidingCase.Cases.One _ -> { }
            case DecidingCase.Cases.EachOf(var alternatives) ->
                    alternatives.forEach(each -> notTakenApartAt(each, figures));
            case DecidingCase.Cases.Together(var factors) ->
                    factors.forEach(each -> notTakenApartAt(each, figures));
            case DecidingCase.Cases.NotTakenApart(var stoppedAt) -> figures.add(stoppedAt);
        }
    }

    /** Whether one more step may be taken — an alternative chosen or a part asked — counting it
     *  where it may. */
    private boolean aStepIsLeft() {
        if (left == 0) {
            return false;
        }
        left--;
        return true;
    }
}
