package souther.compiler.partition;

import java.util.List;
import java.util.Objects;

/**
 * Values put forward for a position, and what of this compiler's the building of them met.
 *
 * <p>Two halves of one answer. A builder stopped by a figure of this compiler's — a list longer
 * than a proposal holds, more pairings than are built at once — hands back fewer values than the
 * type has, and a reader holding the values alone reads that as the type having no more — a set of
 * two of a newtype over a long list read as one nothing can build, where it is one this compiler
 * declined to build. So what was met travels with what was built, through every value
 * built out of it, to the reader that says why nothing came of a search.
 *
 * <p>What a build that ran was stopped by, and not whether the values are all there are. A builder
 * asked for a few stops at a few whatever the type has left, and that is no shortfall; a type with
 * two values offering two is no shortfall either. Nor is it a verdict: values built beside a stop
 * are values, and a row composed of them is a row whatever stopped the others. Which of the two a
 * reader is owed is decided where the search comes back ({@link Generator}), not here.
 *
 * @param values what was built, in the order a caller should reach for them
 * @param met    what of this compiler's the build was stopped by on the way, nothing where none
 */
record Proposals(List<FixtureTemplate> values, CompositionShortfall met) {

    /** Nothing built, and nothing stopped it. */
    static final Proposals NONE = new Proposals(List.of(), CompositionShortfall.NONE);

    Proposals {
        values = List.copyOf(values);
        Objects.requireNonNull(met, "what a build met is nothing, not absent");
    }

    /** These, built with nothing of this compiler's stopping the build. */
    static Proposals of(List<FixtureTemplate> values) {
        return new Proposals(values, CompositionShortfall.NONE);
    }

    /** Nothing, because {@code figure} stopped it. */
    static Proposals stoppedBy(CompositionBudget figure) {
        return new Proposals(List.of(), CompositionShortfall.of(List.of(figure)));
    }

    boolean isEmpty() {
        return values.isEmpty();
    }
}
