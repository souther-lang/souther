package souther.compiler.semantics;

import java.math.BigDecimal;
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
        byPosition = Map.copyOf(normalized);
    }

    /** What the argument at {@code position} reads as, or null where nothing here says. */
    public BigDecimal at(int position) {
        return byPosition.get(position);
    }

    /** Whether this taking was given nothing beside the value it is taken of. */
    public boolean none() {
        return byPosition.isEmpty();
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
