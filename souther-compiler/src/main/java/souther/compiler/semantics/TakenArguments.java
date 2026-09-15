package souther.compiler.semantics;

import java.math.BigDecimal;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.TreeMap;

/**
 * What the arguments of a taking beside the value it is taken of read as.
 *
 * <p><b>Part of which number this is.</b> An operation taking a number of one value may be given
 * others that settle which number it takes — a divisor says which quotient — and two takings that
 * differ only there are two numbers. Left out of what names a term, {@code x / 2} and {@code x / 3}
 * are one subject: a line drawn on either falls on both, and a row composed for one is offered at
 * the other.
 *
 * <p>The constants and not the expressions. What an argument reads as is the reading's answer and a
 * name given a constant is that constant, so {@code x / 2} and a {@code x / TWO} over a constant
 * {@code TWO} are one number and one term. An argument that reads as no constant leaves no entry —
 * and a taking whose account needs one is then a taking nothing here names, which is what
 * {@link souther.compiler.check.NumericMeasures#takenIn} answers with.
 *
 * <p>Held with the scale taken off, so that a number written two ways is one value. Two entries
 * comparing unequal because one of them was written with a nought after the point would be two
 * subjects for one number, which is the collision this exists to stop.
 *
 * @param byPosition what each argument reads as, by the place it stands at in the call
 */
public record TakenArguments(Map<Integer, BigDecimal> byPosition) {

    /** A taking given nothing beside the value it is taken of. */
    public static final TakenArguments NONE = new TakenArguments(Map.of());

    public TakenArguments {
        Map<Integer, BigDecimal> normalized = new TreeMap<>();
        byPosition.forEach((position, read) -> {
            if (position == null || read == null) {
                throw new IllegalArgumentException(
                        "an argument reads as a number at a place, and neither half is absent");
            }
            normalized.put(position, read.stripTrailingZeros());
        });
        // Kept in the order the arguments stand in, because one of these is written out wherever
        // such a number is named and a name a reader looks up has to be the same name twice.
        // `Map.copyOf` promises no order, so what it hands back would spell a taking of two
        // arguments one way today and the other way after a rebuild.
        byPosition = Collections.unmodifiableMap(new LinkedHashMap<>(normalized));
    }

    /** The one argument at {@code position}, read as {@code constant}. */
    public static TakenArguments at(int position, BigDecimal constant) {
        Map<Integer, BigDecimal> one = new LinkedHashMap<>();
        one.put(position, constant);
        return new TakenArguments(one);
    }

    /** What the argument at {@code position} reads as, or null where nothing here says. */
    public BigDecimal at(int position) {
        return byPosition.get(position);
    }

    /** Whether this taking was given nothing beside the value it is taken of. */
    public boolean none() {
        return byPosition.isEmpty();
    }

    /**
     * A taking of {@code value} with these arguments, as a call of it is written: the value and
     * whatever stands beside it, in brackets.
     *
     * <p>One owner for how such a number is spelled, because several readers spell one — a subject,
     * a term, a finding, the name a report shows for a measure. Spelled apiece, the ones that were
     * written before a taking could be given anything would go on naming two numbers of one place
     * alike, and a reader looking one of them up would be given both.
     */
    public String writtenWith(String value) {
        return none() ? "(" + value + ")" : "(" + value + ", " + this + ")";
    }

    /** The arguments as they are written between the brackets, and nothing where there are none. */
    @Override
    public String toString() {
        if (byPosition.isEmpty()) {
            return "";
        }
        StringBuilder out = new StringBuilder();
        byPosition.values().forEach(read -> {
            if (!out.isEmpty()) {
                out.append(", ");
            }
            out.append(read.toPlainString());
        });
        return out.toString();
    }
}
