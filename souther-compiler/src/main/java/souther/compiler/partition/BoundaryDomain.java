package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Granularity;
import souther.compiler.observe.ObservedValue;

import java.util.Optional;

/**
 * What a carrier can say about the counts next to a boundary.
 *
 * <p>Asking for "the value just over the threshold" is asking the carrier, not the threshold. A whole
 * number has a next one; a decimal, in general, does not — {@code 100000.000…1} is not a value the
 * type names, and inventing an epsilon would test a rule the model never stated. Where a carrier
 * cannot answer, the boundary itself is still worth a row and the value beside it is reported as not
 * derivable rather than made up.
 *
 * <p>Counts in and counts out. Each of these used to take an {@link ObservedValue} and check its
 * shape before it could work — a step over an {@code Int} refused anything that was not an
 * {@code ObservedValue.Integer} — which is a carrier's question asked of a value, and the answer to
 * it was silence rather than a build failure. What decides the answer now is which carrier was asked,
 * and turning the count back into a value is the carrier's own.
 */
public interface BoundaryDomain {

    Optional<Count> successor(Count at);

    Optional<Count> predecessor(Count at);

    Optional<Count> midpoint(Count low, Count high);

    /**
     * How the counts beside a boundary on {@code carrier} are found.
     *
     * <p>Read off the spacing and nothing else. Whether a strict bound has a next count to step to is
     * exactly what {@link Granularity} says, so a carrier added to the table gets its neighbours from
     * what it already declared about itself rather than from an entry somebody remembered to add
     * here.
     */
    static BoundaryDomain on(Carrier carrier) {
        if (carrier == null) {
            return NONE;
        }
        Granularity spacing = carrier.spacing();
        return new BoundaryDomain() {
            @Override
            public Optional<Count> successor(Count at) {
                // A carrier with no smallest step has no next count: whether the value after a
                // date-time is a second, a millisecond or a nanosecond later is a decision nobody has
                // taken, and inventing an epsilon would test a rule the model never stated.
                return spacing == Granularity.DISCRETE ? held(at.plus(1)) : Optional.empty();
            }

            @Override
            public Optional<Count> predecessor(Count at) {
                return spacing == Granularity.DISCRETE ? held(at.minus(1)) : Optional.empty();
            }

            @Override
            public Optional<Count> midpoint(Count low, Count high) {
                return held(low.halfwayTo(high, spacing));
            }

            /** Only where the carrier holds it. A step off the end of what a carrier counts is not a
             * value beside anything, and it reaches here the same way from every caller that steps. */
            private Optional<Count> held(Count at) {
                return Optional.ofNullable(carrier.onTheGrid(at));
            }
        };
    }

    /** Nothing has a neighbour here: the position is on no carrier at all. */
    BoundaryDomain NONE = new BoundaryDomain() {
        @Override
        public Optional<Count> successor(Count at) {
            return Optional.empty();
        }

        @Override
        public Optional<Count> predecessor(Count at) {
            return Optional.empty();
        }

        @Override
        public Optional<Count> midpoint(Count low, Count high) {
            return Optional.empty();
        }
    };
}
