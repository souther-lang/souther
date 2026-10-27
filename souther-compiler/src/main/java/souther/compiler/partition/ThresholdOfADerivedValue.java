package souther.compiler.partition;

import java.util.Objects;

/**
 * One place a computation cut at several places is cut, which is what an ON and an OFF point are
 * owed for once for each of them.
 *
 * <p>The computation and the place, and never the place alone: one comparison read at two calls
 * cut at different places is two computations, and a row on a border of one is on no border of the
 * other. And never the computation alone, which is what the weights are owed for — a weight is a
 * fault of the computation, while a shifted threshold is a fault of one of its places, and a row at
 * the points of one place says nothing about where another is.
 *
 * <p>The place as the computation is cut at it and not the value the table holds. A total weighed
 * into an average is cut where the average reaches the threshold, and that is where a row has to
 * stand.
 */
public record ThresholdOfADerivedValue(DerivedValue value, DerivedValue.Place place) {

    public ThresholdOfADerivedValue {
        Objects.requireNonNull(value, "a threshold is a threshold of some computation");
        Objects.requireNonNull(place, "a computation is cut at some place");
    }
}
