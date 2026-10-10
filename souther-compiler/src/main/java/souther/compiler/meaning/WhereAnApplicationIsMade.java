package souther.compiler.meaning;

import souther.compiler.inputs.TermPath;
import souther.compiler.semantics.HowAClosureIsApplied;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
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
     * @param answers what the closure answers on each application, in that order. Read only where
     *                the operation stops on an answer, so it may be null elsewhere
     * @param applications how many applications there are
     * @param how     how far the operation goes applying the closure
     * @param outer   what has to hold for a run to be inside the closure at all
     */
    public static List<Proposition> reached(List<Proposition> answers, int applications,
                                            HowAClosureIsApplied how, Proposition outer) {
        Objects.requireNonNull(outer, "a closure is reached under something, if only nothing");
        List<Proposition> out = new ArrayList<>();
        List<Proposition> before = new ArrayList<>();
        before.add(outer);
        for (int at = 0; at < applications; at++) {
            out.add(Proposition.all(before));
            switch (how) {
                case TO_EVERY_ELEMENT -> { }
                case UNTIL_ONE_HOLDS -> before.add(answers.get(at).denied());
                case UNTIL_ONE_FAILS -> before.add(answers.get(at));
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
     * What has to hold for a run to be inside a closure whose parameters are handed what
     * containers hold, under {@code outer}: each parameter is handed something, from one of the
     * containers it may be handed it from, which then holds something. Said where the values they
     * hold are not written out, and so no application is said; an operation may stop before it
     * makes any, so this is necessary for an application and not enough for one.
     *
     * @param takenFrom for each parameter, the positions of the containers it may be handed
     *                  something from, none of them empty
     */
    public static Proposition whereTheContainersHoldSomething(Proposition outer,
                                                              List<List<TermPath>> takenFrom) {
        List<Proposition> each = new ArrayList<>();
        each.add(outer);
        for (List<TermPath> containers : takenFrom) {
            each.add(Proposition.any(containers.stream()
                    .<Proposition>map(at -> new Proposition.Some(at, nothingAsked(), true))
                    .toList()));
        }
        return Proposition.all(each);
    }

    /** Whether {@code cases} say a line decides wherever a row is. */
    public static boolean everywhere(List<Proposition> cases) {
        return cases.equals(List.of(nothingAsked()));
    }

    /** What has to hold to reach a place an application reaches under {@code reached}, past a
     *  condition met on the way that came out as {@code stated} says. */
    public static Proposition past(Proposition reached, Proposition stated) {
        return Proposition.all(List.of(reached, stated));
    }

    /**
     * One reading of a line, on one application: where the line decides on it, and what has to
     * hold for a run to make it.
     *
     * @param cases   where the line decides on this application, as cases any one of which is
     *                enough; empty where it decides nowhere on it
     * @param reached what has to hold for a run to make this application
     */
    public record OnOne(List<Proposition> cases, Proposition reached) {

        public OnOne {
            cases = List.copyOf(cases);
            Objects.requireNonNull(reached, "an application is made under something");
        }

        /** A line that decides wherever a row is on the application, made under {@code reached}. */
        public static OnOne wherever(Proposition reached) {
            return new OnOne(List.of(nothingAsked()), reached);
        }
    }

    /**
     * Where a line read on each of {@code readings} decides, as cases any one of which is enough:
     * each case of where it decides on one application, met where that application is made.
     *
     * <p>Each case kept once. A case holding wherever a row is makes every other say nothing more,
     * and one holding nowhere says nothing. Past {@link WhereEachLineDecides#MOST_CASES}, the cases
     * are said as one: some one of them holding.
     */
    public static List<Proposition> decidesOn(List<OnOne> readings) {
        Map<String, Proposition> kept = new LinkedHashMap<>();
        for (OnOne one : readings) {
            for (Proposition each : one.cases()) {
                Proposition met = Proposition.all(List.of(each, one.reached()));
                switch (met) {
                    case Proposition.Always(boolean holds) when holds -> {
                        return List.of(met);
                    }
                    case Proposition.Always _ -> { }
                    default -> kept.putIfAbsent(met.key(), met);
                }
            }
        }
        List<Proposition> cases = List.copyOf(kept.values());
        return cases.size() <= WhereEachLineDecides.MOST_CASES ? cases
                : List.of(Proposition.any(cases));
    }
}
