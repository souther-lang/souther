package souther.compiler.inputs;

/**
 * A position, once a name has been resolved to it.
 *
 * <p>What a rule wrote is a name in some value's own words ({@link RuleAddress}); what a row writes
 * is a value at a position. The two are told apart by their types so that neither can be used where
 * the other belongs: a reader holding one of these cannot look a position up by what a rule called
 * it, and a reader holding an address cannot pass it off as somewhere a row goes.
 *
 * <p>The path and nothing else, because a position is where it is. What it holds, what its rules
 * leave it and what a report calls it are the reading's to answer, and each of them is asked of the
 * reading with one of these in hand.
 */
public record PositionId(TermPath at) {

    public PositionId {
        if (at == null) {
            throw new IllegalArgumentException("a position is somewhere");
        }
    }

    @Override
    public String toString() {
        return at.toString();
    }
}
