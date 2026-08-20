package souther.compiler.check;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * What came of trying to read one clause statically: either the reading ran to the end and says what
 * it made of it, or it stopped and says nothing.
 *
 * <p>Two arms, because they are different kinds of sentence. "The reading finished, and this clause
 * is outside what it reads" is a conclusion about the clause. "The reading did not finish" is a fact
 * about this compiler on this run, and it settles nothing about the clause at all — whether the
 * clause is inside the fragment is exactly what was not found out. Held as one answer, an author is
 * told that no guard discharges their construction because an analysis fell over on it, and nothing
 * fails while that is happening, since a stop and a negative conclusion are both silent.
 *
 * <p>The distinction has to be made here rather than remembered downstream. Every reader of a
 * classification reaches this type, and a reader handed one word for both would have to know which
 * of them it had — which is a thing to get right once per reader instead of once.
 */
public sealed interface CapabilityResult {

    /**
     * The reading ran to the end, and this is what it made of the clause.
     *
     * <p>Never empty. A reading that finished has an answer, and an empty set is what a reading that
     * never ran would produce as well — so the arm a clause falls into when nothing was carried has
     * to be one somebody wrote down ({@link StaticReading.Decided},
     * {@link StaticReading.OutsideTheFragment}) rather than the absence of one. An empty set here was
     * how a clause that holds of every value came to be reported as one no guard discharges.
     */
    record Analyzed(Set<StaticReading> readings) implements CapabilityResult {

        public Analyzed {
            if (readings == null || readings.isEmpty()) {
                throw new IllegalArgumentException(
                        "a reading that finished says what it made of the clause");
            }
            // Insertion order: `Set.of` and `Set.copyOf` iterate in an order salted once per JVM
            // run, and these are shown to an author a line at a time.
            readings = Collections.unmodifiableSet(new LinkedHashSet<>(readings));
        }

        public static Analyzed of(StaticReading... readings) {
            return new Analyzed(new LinkedHashSet<>(List.of(readings)));
        }
    }

    /**
     * The reading stopped, so there is no conclusion about the clause.
     *
     * <p>{@code where} is for whoever is working out why, and is not published. What a document says
     * out of this arm is that this compiler did not finish; it names nothing about the clause,
     * because nothing about the clause was established.
     */
    record AnalysisStopped(String where) implements CapabilityResult {

        public AnalysisStopped {
            if (where == null) {
                throw new IllegalArgumentException("a reading that stopped says where it was");
            }
        }
    }
}
