package souther.compiler.partition;

/**
 * What a border asks of the rows in one of its four roles: a row to write, or a reason there is none
 * to ask for.
 *
 * <p>Two answers held apart so that the second cannot be spelled by leaving something out. Every one
 * of these reasons used to be an obligation that was never built — the rules refusing the far side of
 * a bound, a carrier with no name for the value one step over, a side one value wide — and all three
 * reached a reader as the same thing: a list with one fewer entry in it. A reader counting the four
 * items a border owes found this compiler short and was never told which of the three had happened,
 * and two of them are not shortfalls at all.
 *
 * <p>Sealed, and the border answers with one of these for every role. What that buys is that a role
 * cannot go missing: an item nobody built is a compile error at the place that builds them, where a
 * missing entry in a list is nothing at all.
 */
public sealed interface Demand {

    /** A row is asked for, and this is what it has to do. */
    record Owed(Criterion criterion) implements Demand {}

    /** No row is asked for here, and this is what settles it. */
    record NotOwed(NotOwedReason reason) implements Demand {}

    /** The criterion where one is asked for, or null where none is. */
    default Criterion criterion() {
        return this instanceof Owed owed ? owed.criterion() : null;
    }

    /**
     * Whether two readings ask a row for the same thing here.
     *
     * <p>Asked rather than left to {@link #equals}, because a criterion holds levels and a level
     * keeps the spelling the rule was written in ({@link Criterion#sameAs}). Two readings of one
     * line that differ only in how a number was written have not disagreed, and a check that read
     * them as disagreeing would name the identity as wrong over a spelling.
     */
    default boolean sameAs(Demand other) {
        return switch (this) {
            case NotOwed not -> other instanceof NotOwed also && not.reason() == also.reason();
            case Owed owed -> other instanceof Owed also
                    && owed.criterion().sameAs(also.criterion());
        };
    }

    /**
     * Whether the model itself discharged this point, as against this language having no way to name
     * it or the side holding nothing.
     *
     * <p>What a report counts as excluded. The other reasons are counted out too, and they are
     * counted out for reasons a reader acts on differently — so the word is put on the one it belongs
     * to rather than on every point nobody is owed.
     */
    default boolean excluded() {
        return this instanceof NotOwed not && not.reason() == NotOwedReason.THE_RULES_REFUSE_IT;
    }
}
