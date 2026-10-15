package souther.compiler.partition;

import java.util.List;

/**
 * What a comparison states about one position, and the line it was read off.
 *
 * <p>Held together until the name the position is written at has been filed. A field every case of
 * a sum spreads is one name and as many quantities as there are cases, and each case's rules can
 * leave its quantity less room than the name had: a line the name runs as far as can be one a case
 * stops short of. Whether a line reaches its quantity is asked of the line, so filing moves the line
 * to each case and asks there — the evidence alone has a place the values part and nothing to say
 * whether a case's values get that far.
 *
 * @param evidence what the rule states about the position, as the comparison was read
 * @param line     the line it was read off, on the quantity the rule was written about
 */
public record LineEvidence(RuleEvidence evidence, Cutting line) {

    public LineEvidence {
        if (evidence instanceof RuleEvidence.BySet) {
            throw new IllegalArgumentException(
                    "a set told from the rest is read off no line: " + evidence);
        }
    }

    /**
     * The rule that drew the line, as this reading met it.
     *
     * <p>A line's origin, which is what the two kinds of evidence read off a line both carry. The
     * third kind is read off no line and is refused where one of these is made.
     */
    public LineOrigin by() {
        return switch (evidence) {
            case RuleEvidence.Divides it -> it.by();
            case RuleEvidence.Singles it -> it.by();
            case RuleEvidence.BySet it -> throw new IllegalStateException(
                    "a set told from the rest is read off no line: " + it);
        };
    }

    /** What each of {@code read} states, in the order they were read. */
    static List<RuleEvidence> statedIn(List<LineEvidence> read) {
        return read.stream().map(LineEvidence::evidence).toList();
    }
}
