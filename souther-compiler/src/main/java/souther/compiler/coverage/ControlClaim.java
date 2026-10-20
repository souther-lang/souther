package souther.compiler.coverage;

import java.util.List;
import java.util.Optional;

/**
 * Something a run can be held to: that it passed one place, coming out one way.
 *
 * <p>The one thing a reading of the model may assert about a run, and the only shape a certification
 * has to know. A claim is a place and nothing about why anyone is interested in it — which is what
 * keeps whatever is doing the reading and whatever records the running from growing into each other.
 * The reading's own vocabulary changes as the reading gets better; that a comparison came out false
 * does not.
 *
 * <p>Not every place is one of these. A place no run could be recorded at is one a claim could never
 * be satisfied at, which is worse than no claim at all: it reads as a combination that was tried and
 * missed. {@link #of} is where that is decided, so a claim that exists is one an observation can
 * answer.
 *
 * <p><b>Which place, and which of a run's visits to it, are two things.</b> A place is a construct of
 * the tree that runs and is the same construct however often a run comes back to it. Which visit an
 * observation is asked about is a condition on the evidence and says nothing about what the place
 * is, so it is held beside the place and not made part of it ({@link Visit}). Whether the nth visit
 * is the visit that belongs to some value is the reading's to have shown, and nothing here decides it.
 *
 * @param at    the place
 * @param visit which of a run's visits to it the claim is about
 */
public record ControlClaim(ControlPlace at, Visit visit) {

    public ControlClaim {
        if (at == null || visit == null) {
            throw new IllegalArgumentException("a claim is a claim about somewhere, on some visit");
        }
        if (visit instanceof Visit.Nth && !(at instanceof ControlPlace.Outcome)) {
            throw new IllegalArgumentException("only a condition coming out a way is recorded"
                    + " visit by visit, and " + at + " is not one");
        }
    }

    /** Which of the times a run passes a place a claim is about. */
    public sealed interface Visit {

        /** Some visit: the run passed the place, coming out the way, at least once. */
        Visit ANY = new Any();

        /** Whichever visits there were. */
        record Any() implements Visit { }

        /**
         * The {@code index}th visit, counting from none, in the order the run makes them.
         *
         * <p>Only the first {@link RecordedVisit#MOST} are recorded. A claim names one beyond
         * that only in a group that is not measured, because the figure is out of reach of any
         * budget a group of combinations can be offered under.
         */
        record Nth(int index) implements Visit {

            public Nth {
                if (index < 0) {
                    throw new IllegalArgumentException("visits are counted from none: " + index);
                }
            }
        }
    }

    /**
     * The claim that a run passed {@code at}, or empty where no run could be recorded there.
     *
     * <p>Empty is an ordinary answer and the safe direction: what cannot be witnessed cannot be
     * claimed, so whatever was going to be built on it is left unbuilt rather than built and never
     * satisfiable.
     *
     * <p>One rule, read off whichever half of the place answers it. An arm carries its probe and
     * says outright whether it has one. A comparison coming out one way exists only where the plan
     * numbered the comparison — which the plan does for a comparison standing where a row can get to
     * and where what it stands in answers a value — so a {@link ControlPlace.Outcome} that exists is
     * one a run can be recorded at, and one in a position no run reaches is a place the plan makes
     * no outcome for at all.
     */
    public static Optional<ControlClaim> of(ControlPlace at) {
        return switch (at) {
            case ControlPlace.Arm arm -> arm.isMeasured()
                    ? Optional.of(new ControlClaim(arm, Visit.ANY)) : Optional.empty();
            case ControlPlace.Outcome outcome ->
                    Optional.of(new ControlClaim(outcome, Visit.ANY));
        };
    }

    /**
     * The claim that a run's {@code index}th visit to {@code at} came out the way it says.
     *
     * <p>Not empty where {@link #of} would be: a comparison numbered by the plan is one a run is
     * recorded at on every visit.
     */
    public static ControlClaim onVisit(ControlPlace.Outcome at, int index) {
        return new ControlClaim(at, new Visit.Nth(index));
    }

    /**
     * Whether {@code seen} did this.
     *
     * <p>Existential, the way every measure over a run here is: a row that passed the place passed
     * it. What this does not say is how many times, which is why a claim is only made of some visit
     * where a run passes the place once ({@link CoverageSites.Plan#mayRepeat}), and of a named one
     * where it comes back to it.
     */
    public boolean satisfiedBy(AlignedObservation seen) {
        return switch (at) {
            case ControlPlace.Arm arm ->
                    arm.probe().isPresent() && seen.lit(arm.probe().get());
            case ControlPlace.Outcome outcome -> switch (visit) {
                case Visit.Any _ -> seen.saw(outcome.at(), outcome.held());
                case Visit.Nth(int index) -> seen.sawOnVisit(outcome.at(), index, outcome.held());
            };
        };
    }

    /**
     * Whether a run that did this did not do {@code other}: one condition coming out two ways on the
     * same visit, or two arms of one fork.
     *
     * <p>What tells two ways apart by what a run is seen doing, since a run passes a place a claim
     * is made at once or on a visit it names. Two claims that are not one of these may both be made
     * by one run, and a run seen at one is not shown not to be at the other.
     */
    public boolean excludes(ControlClaim other) {
        return switch (visit) {
            case Visit.Any _ -> other.visit instanceof Visit.Any && at.excludes(other.at);
            case Visit.Nth(int index) -> other.visit instanceof Visit.Nth(int there)
                    && there == index && at.excludes(other.at);
        };
    }

    /**
     * Whether what a run is seen doing tells each of {@code ways}, each the claims a run on it is
     * held to, from every other: each two claim some place a run passes once, one way on one and
     * another way on the other ({@link #excludes}).
     *
     * <p>A claim on one way is passed by a run on another wherever the other passes that place the
     * same way — or says nothing of how it passed it. Two ways told apart by nothing else are proved
     * by one run as well as by the other.
     */
    public static boolean toldApart(List<List<ControlClaim>> ways) {
        for (int one = 0; one < ways.size(); one++) {
            for (int other = one + 1; other < ways.size(); other++) {
                if (!onePassedWhereTheOtherDidNot(ways.get(one), ways.get(other))) {
                    return false;
                }
            }
        }
        return true;
    }

    private static boolean onePassedWhereTheOtherDidNot(List<ControlClaim> one,
                                                        List<ControlClaim> other) {
        for (ControlClaim mine : one) {
            for (ControlClaim theirs : other) {
                if (mine.excludes(theirs)) {
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public String toString() {
        String place = switch (at) {
            case ControlPlace.Arm arm -> "arm " + arm.arm();
            case ControlPlace.Outcome outcome -> outcome.toString();
        };
        return visit instanceof Visit.Nth(int index) ? place + " on visit " + index : place;
    }
}
