package souther.compiler.check;

import souther.compiler.types.Type;

/**
 * What a reading that opens a name finds beneath it, kept so that the next reading to open the same
 * name does not open everything beneath it again.
 *
 * <p>A name worn over a value is opened wherever it is reached, and what it wraps may be another
 * name worn over a value, and so on down. Opening each one reads that name's count and goes on into
 * what it wraps, and what the reading at the top came to is every one of those counts taken
 * together with what is at the bottom. The counts are the names' own and the same whoever opens
 * them; only what is at the bottom is read under the rules of whoever is opening. So the counts are
 * taken together once, where each name is answered, and a reading opening the top name takes that
 * one count with what it finds at the bottom.
 *
 * <p>Taken together the way {@link CardinalityTransfer#throughTheName} takes two of them, which is
 * what makes one count enough. Every count read off a name is a count or a proof that stops at the
 * name, and between those, taking a name's count with what was found beneath it gives the same
 * answer however the names beneath were grouped.
 *
 * <p>A reading with no rules of its own at the place it opens the name — what a collection holds,
 * whatever is beneath that — reads the bottom the same way whoever is opening, so the whole of it is
 * kept too. Without it, a chain of names each wrapping a collection of the one before would be
 * opened all the way down at every link, as deep as it is long.
 *
 * @param terminal  what the last name opened wraps, read under the rules of whoever opens the top
 *                  one; null where the reading stops at the names and reads nothing beneath them
 * @param standsFor the counts of every name opened on the way down, taken together
 * @param unruled   what opening the name comes to where no rule is written about the place it is
 *                  opened at
 */
public record Unwrapping(Type terminal, Cardinality standsFor, Cardinality unruled) {

    public Unwrapping {
        if (standsFor == null || unruled == null) {
            throw new IllegalArgumentException("what a name opens onto is a count");
        }
    }

    /** A reading that stops at a name with {@code count} and reads nothing beneath it. */
    static Unwrapping stoppingAt(Cardinality count) {
        return new Unwrapping(null, count, count);
    }

    /** A name with {@code count} opened onto {@code terminal}, with no name beneath it known, where
     *  {@code terminal} read under no rule came to {@code unruled}. */
    static Unwrapping onto(Type terminal, Cardinality count, Cardinality unruled) {
        return new Unwrapping(terminal, count, CardinalityTransfer.throughTheName(count, unruled));
    }

    /** A name with {@code count} opened onto the name this one is the opening of. */
    Unwrapping beneath(Cardinality count) {
        return new Unwrapping(terminal, CardinalityTransfer.throughTheName(count, standsFor),
                CardinalityTransfer.throughTheName(count, unruled));
    }
}
