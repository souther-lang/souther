package souther.compiler.partition;

/**
 * Where a rule divides a {@link BorderQuantity}: the threshold it names.
 *
 * <p>Not a point of the border. The threshold is what the rule wrote and the points are what the
 * quantity can take either side of it, and the two are only ever the same level by coincidence —
 * {@code 2 * a <= 9} names nine, and nine is not a value {@code 2 * a} takes. Held as one type, a
 * report printed the threshold where a row was owed and a search looked for a row at a level nothing
 * stands at.
 *
 * <p>Apart from {@link Cut}, which is a place on a <em>position's</em> order together with every rule
 * that put a cut there and the merging that makes one position's cuts an exclusive partition. That is
 * an axis's business and stays there: this is the threshold alone, on the order of whatever the rule
 * happened to cut.
 *
 * <p>Which way the rule is satisfied is not here either. That is the rule's, and {@link OriginRef}
 * already carries it — written here as well, the two would be free to disagree about one rule.
 */
public record QuantityCut(Level at) {

    public QuantityCut {
        if (at == null) {
            throw new IllegalArgumentException("a cut is at a level");
        }
    }

    /** The same place with its level written the one way, for a reader comparing two of these as
     *  places rather than as they were written ({@link Level#canonical()}). */
    public QuantityCut canonical() {
        return new QuantityCut(at.canonical());
    }
}
