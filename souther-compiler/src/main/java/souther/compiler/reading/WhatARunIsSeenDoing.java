package souther.compiler.reading;

import souther.compiler.check.ScopeStep;
import souther.compiler.core.Core;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.flow.ComparisonWays;
import souther.compiler.flow.Naming;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

/**
 * The ways along a body as what a run that took them would be seen doing, and nothing about the
 * inputs.
 *
 * <p>The naming for a reader that holds a row to a way and runs it to see. Which input position a
 * decision is about is what composing a row by classes needs, and a comparison of a number no
 * position holds — what a list's elements add up to — has no such answer, so {@link CoverageNaming}
 * says nothing of it. Which comparison it is and which way it came out are still read off the
 * comparison, and they are all a run is checked against ({@link ControlClaim#satisfiedBy}).
 *
 * <p>Made at the node, as {@link Decision} is made. The walk that reads the body meets each
 * comparison and each arm and takes the claim off it there; nothing here goes looking through a
 * condition for the comparisons it is spelled with, which would take one under a call's argument
 * for one the condition decides by, and would lose which way each has to come out.
 */
final class WhatARunIsSeenDoing implements Naming<List<ControlClaim>> {

    private final CoverageSites.Plan plan;

    WhatARunIsSeenDoing(CoverageSites.Plan plan) {
        this.plan = plan;
    }

    /**
     * Every comparison the plan records coming out either way, and the reading of the tree for
     * everything else.
     *
     * <p>For a reader that runs what it composes. Whether some value brings a comparison out a way
     * is what keeps a reading from listing a way the body has not got, and a reading whose ways a
     * row is checked against by running it does not need that: a way no value takes is one no row
     * is seen going, and the row is not taken. What it does need is each way that may be there,
     * including those through a comparison nothing could say varies.
     */
    ComparisonWays eitherWay() {
        return new ComparisonWays() {
            @Override
            public boolean comesOut(Core e, boolean want, Function<Core.Read, Core> settledBy) {
                if (outcomeAt(e, want).isPresent()) {
                    return true;
                }
                return ComparisonWays.OF_THE_TREE.comesOut(e, want, settledBy);
            }

            @Override
            public ComparisonWays entering(ScopeStep step) {
                return this;
            }
        };
    }

    @Override
    public List<ControlClaim> nowhere() {
        return List.of();
    }

    /** Both, or null where one says a place came out one way and the other the other way. */
    @Override
    public List<ControlClaim> join(List<ControlClaim> held, List<ControlClaim> more) {
        List<ControlClaim> both = new ArrayList<>(held);
        for (ControlClaim each : more) {
            if (both.contains(each)) {
                continue;
            }
            for (ControlClaim already : both) {
                if (otherWayOut(already.at(), each.at())) {
                    return null;
                }
            }
            both.add(each);
        }
        return List.copyOf(both);
    }

    /** Whether the two are one place a run passes coming out two ways. */
    private static boolean otherWayOut(ControlPlace one, ControlPlace other) {
        return switch (one) {
            case ControlPlace.Outcome outcome -> other instanceof ControlPlace.Outcome that
                    && that.at().equals(outcome.at()) && that.held() != outcome.held();
            case ControlPlace.Arm arm -> other instanceof ControlPlace.Arm that
                    && that.arm().fork().equals(arm.arm().fork())
                    && that.arm().part() != arm.arm().part();
        };
    }

    // What a run is seen doing does not turn on what a name reads.
    @Override
    public WhatARunIsSeenDoing entering(ScopeStep step) {
        return this;
    }

    @Override
    public List<ControlClaim> side(Core value, boolean held) {
        return outcomeAt(value, held)
                .flatMap(ControlClaim::of)
                .map(List::of)
                .orElse(null);
    }

    /**
     * Where a run is seen bringing {@code value} out {@code held}: at the comparison it is, or at
     * the application of one of the language's operations whose answer it is — or empty where the
     * plan records neither.
     */
    private Optional<ControlPlace.Outcome> outcomeAt(Core value, boolean held) {
        Core e = Core.withoutStanding(value);
        if (e instanceof Core.Binary comparison) {
            return CoverageNaming.outcomeAt(plan, comparison, held);
        }
        return plan.applicationAnsweringAt(e)
                .flatMap(application -> plan.outcomeOf(application, held));
    }

    @Override
    public List<ControlClaim> matchCase(Core.Match match, int part) {
        return armOf(match, part);
    }

    @Override
    public List<ControlClaim> forkArm(Core fork, int part) {
        return armOf(fork, part);
    }

    /** That a run went down arm {@code part} of {@code fork}, or null where nothing records it. */
    private List<ControlClaim> armOf(Core fork, int part) {
        ControlPlace.Arm[] arms = plan.armsOf(fork);
        if (arms == null || part >= arms.length || arms[part] == null) {
            return null;
        }
        return ControlClaim.of(arms[part]).map(List::of).orElse(null);
    }

    @Override
    public int mostArrivals() {
        return CoverageNaming.MOST_OUTCOMES;
    }
}
