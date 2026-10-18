package souther.compiler.meaning;

import souther.compiler.semantics.HowAClosureIsApplied;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * What has to hold for a run to make each application of a closure handed the values a container
 * was written with, and where a line read on several of those applications decides.
 *
 * <p><b>Said of the applications in the order a run makes them, and before anything is made of
 * what each states.</b> {@code List.any(x -> x > 5, [a, b])} applies the closure to {@code b} only
 * where its application to {@code a} answered false, and {@code List.any(x -> x > 5, [b, a])}
 * the other way round. What the applications state is the same set of statements either way, so
 * which of them a run reaches is read off the order and not off the statements; and two
 * applications stating the same thing are still two applications, each reached its own way.
 *
 * <p><b>A line read on several applications is one line, read once on each.</b> Where it decides is
 * where any one of those readings does: where it decides on an application, met where that
 * application is made. A reading reached nowhere adds nothing, and one reached wherever the line
 * decides makes the others say nothing more.
 */
public final class WhereAnApplicationIsMade {

    private WhereAnApplicationIsMade() {
    }

    /**
     * What has to hold for a run to make each application, in the order a run makes them.
     *
     * <p>An application is made where the container holds the element it is handed, and an
     * operation stopping on an answer stops on one it made: an element a filter dropped answers
     * nothing, and the applications after it are made as they would be without it. And it is made
     * only where every application before it answered: one that answers nothing on some rows — a
     * quotient by the value it was handed, at nought — stops the run there, however far the
     * operation would have gone.
     *
     * @param answers what the closure answers on each application, in that order. Read where the
     *                operation stops on an answer, or where an application may answer nothing, so
     *                it may be null elsewhere
     * @param keptBy  for each application, the truths each of which holds where the container
     *                holds the element it is handed — none where it holds it whatever the row is
     * @param how     how far the operation goes applying the closure
     * @param outer   what has to hold for a run to be inside the closure at all
     */
    public static List<Proposition> reached(List<Proposition> answers,
                                            List<List<Proposition>> keptBy,
                                            HowAClosureIsApplied how, Proposition outer) {
        Objects.requireNonNull(outer, "a closure is reached under something, if only nothing");
        List<Proposition> out = new ArrayList<>();
        List<Proposition> before = new ArrayList<>();
        before.add(outer);
        for (int at = 0; at < keptBy.size(); at++) {
            Proposition kept = Proposition.all(keptBy.get(at));
            List<Proposition> here = new ArrayList<>(before);
            here.add(kept);
            out.add(Proposition.all(here));
            switch (how) {
                // Whatever it answered, but it answered: one that stopped the run is the last.
                case TO_EVERY_ELEMENT -> {
                    Proposition answered = answers == null ? null
                            : Proposition.whereItAnswersAtAll(answers.get(at));
                    if (answered != null) {
                        before.add(Proposition.any(List.of(kept.denied(), answered)));
                    }
                }
                // Answered, and the other way: what a run got past holds on every row or fails.
                case UNTIL_ONE_HOLDS -> before.add(Proposition.any(List.of(kept.denied(),
                        Proposition.whereItHolds(answers.get(at).denied()))));
                case UNTIL_ONE_FAILS -> before.add(Proposition.any(List.of(kept.denied(),
                        Proposition.whereItHolds(answers.get(at)))));
                case AT_MOST_ONE, TO_SOME -> throw new IllegalArgumentException("which values an"
                        + " operation applies its closure to is not said, so no application of it"
                        + " is placed among the others");
            }
        }
        return List.copyOf(out);
    }

    /** What has to hold to be inside no closure at all, which is nothing. */
    public static Proposition nothingAsked() {
        return new Proposition.Always(true);
    }

    /**
     * What has to hold for a run to be inside a closure that only operations apply, under
     * {@code outer}: one of the containers they apply it over holds something. Said where the
     * values they hold are not written out, and so no application is said; an operation may stop
     * before it makes any, so this is necessary for an application and not enough for one.
     *
     * <p>An option is a container of one value at most, and the closure is applied to that value
     * where the option holds one: what holds there is that it holds a value, and no statement about
     * some element of it, which would ask how many it holds of something that holds one or none.
     *
     * @param holding the positions of the containers, one for each operation applying the closure
     *                to every element of one
     * @param present the positions of the options, one for each operation applying the closure to
     *                the value one holds
     */
    public static Proposition whereOneOfTheContainersHoldsSomething(Proposition outer,
                                                                    List<DecisionSubject> holding,
                                                                    List<DecisionSubject> present) {
        List<Proposition> any = new ArrayList<>();
        holding.forEach(at -> any.add(new Proposition.Some(at, nothingAsked(), true)));
        present.forEach(at -> any.add(new Proposition.Present(at, true)));
        return past(outer, Proposition.any(any));
    }

    /**
     * Whether {@code cases} say a line decides wherever a row is: one case, holding wherever a row
     * is and standing for itself. Said for several, it decides only where rows on both sides of
     * the line are in one of them, which is not wherever a row is.
     */
    public static boolean everywhere(List<DecidingCase> cases) {
        return cases.size() == 1 && cases.getFirst().saidAlone()
                && cases.getFirst().condition().equals(nothingAsked());
    }

    /** What has to hold to reach a place an application reaches under {@code reached}, past a
     *  condition met on the way that came out as {@code stated} says. */
    public static Proposition past(Proposition reached, Proposition stated) {
        return Proposition.all(List.of(reached, stated));
    }

    /**
     * What has to hold for a run to get somewhere by any of {@code ways}: one of them holding, and
     * nowhere at all where there is none.
     */
    public static Proposition alongOneOf(List<Proposition> ways) {
        return ways.isEmpty() ? new Proposition.Always(false) : Proposition.any(ways);
    }

    /**
     * One reading of a line, on one application: where the line decides on it, and what has to
     * hold for a run to make it.
     *
     * @param cases   where the line decides on this application, as cases any one of which is
     *                enough; empty where it decides nowhere on it
     * @param reached what has to hold for a run to make this application
     */
    public record OnOne(List<DecidingCase> cases, Proposition reached) {

        public OnOne {
            cases = List.copyOf(cases);
            Objects.requireNonNull(reached, "an application is made under something");
        }

        /** A line that decides wherever a row is on the application, made under {@code reached}. */
        public static OnOne wherever(Proposition reached) {
            return new OnOne(List.of(DecidingCase.alone(nothingAsked())), reached);
        }
    }

    /**
     * Where a line read on each of {@code readings} decides, as cases any one of which is enough:
     * each case of where it decides on one application, met where that application is made.
     *
     * <p>Each case kept once, and two said by one condition taken as one ({@link DecidingCase#and}).
     * A case holding wherever a row is, and standing for itself, makes every other say nothing
     * more; one holding nowhere says nothing. Cases that differ only in which case one value is are
     * said as one ({@link WhereEachLineDecides#joinedOverAValue}); past
     * {@link WhereEachLineDecides#MOST_CASES} after that, the cases are said as one: some one of
     * them holding, said for each of them.
     */
    public static List<DecidingCase> decidesOn(List<OnOne> readings) {
        List<DecidingCase> kept = new ArrayList<>();
        for (OnOne one : readings) {
            for (DecidingCase each : one.cases()) {
                DecidingCase met = each.meeting(one.reached());
                switch (met.condition()) {
                    case Proposition.Always(boolean holds) when holds && met.saidAlone() -> {
                        return List.of(met);
                    }
                    case Proposition.Always(boolean holds) when !holds -> { }
                    case Proposition.Always _, Proposition.Compared _, Proposition.Truth _,
                         Proposition.InCases _, Proposition.Present _, Proposition.SameValue _,
                         Proposition.LastToHold _, Proposition.All _, Proposition.Any _,
                         Proposition.Some _, Proposition.Carried _, Proposition.SomeReachable _,
                         Proposition.Unread _, Proposition.OnAnApplication _,
                         Proposition.SoManyHold _, Proposition.WhereItAnswers _ -> kept.add(met);
                }
            }
        }
        return DecidingCase.saidInAsFewAsMay(WhereEachLineDecides.joinedOverAValue(
                DecidingCase.oneForEachCondition(kept)));
    }
}
