package souther.compiler.coverage;

/**
 * One comparison coming out one way, as a run records it.
 *
 * <p>Recorded from the comparison's own value and never worked out from the arm that follows it. A
 * condition stops as soon as it is settled, so under {@code A && B} the arm taken when the condition
 * fails is reached both by a value that made {@code B} false and by one that never evaluated
 * {@code B} — the arm cannot say which, and a reading that recovered the way out of it would be
 * guessing at exactly the point a claim about the comparison is made.
 *
 * <p>Three states and not two, which is what having these at all buys. A comparison can have come
 * out one way, come out the other, or not have been reached: the first two are one of these being
 * recorded and the third is neither of them being, and nothing else in a run's record can tell the
 * third from the other two.
 *
 * @param at   which comparison
 * @param held the way it came out
 */
public record ComparisonOutcome(ComparisonOccurrence at, boolean held) {

    public ComparisonOutcome {
        if (at == null) {
            throw new IllegalArgumentException("a way a comparison came out is a way of one");
        }
    }

    @Override
    public String toString() {
        return at + (held ? " held" : " failed");
    }
}
