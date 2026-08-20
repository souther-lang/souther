package souther.compiler.types;

/**
 * What a module's scope answers about a name written in it.
 *
 * <p>Three answers, and the third is why this is a type. A name may denote a declaration; a name
 * may be in scope and denote nothing; and nothing here may be written that way at all. The middle
 * one is not an absence: an import line that could not do its job is reported on that line, and the
 * names it was to bring in stay in scope denoting nothing, so that a use of one takes the error
 * type and says nothing more. Left out of scope instead, every use would be reported as an unknown
 * type, which sends the author to a use when what is wrong is the import.
 *
 * <p>What parts the two that denote nothing is whether anything has been said yet, so that is what
 * they are named for. {@code StandsForNothing} and {@code NotInScope} are read the same way round
 * by everyone; {@code Nothing} and {@code Unknown}, which is what they were called first, are two
 * words for the same thing and were read for each other within a day of being written.
 *
 * <p>The three used to be a {@link TypeSymbol} that was null, a {@link TypeSymbol} of a module no
 * source may name ({@code souther.unresolved}), and a {@link TypeSymbol} — so a reader that took the
 * answer for a declaration was reading a fabricated identity, and eight of them asked
 * {@code isUnresolved()} afterwards to find out. An answer that has to be asked what it is is an
 * answer a reader can forget to ask.
 */
public sealed interface Denotation {

    /** The declaration the name denotes here. */
    record Denotes(TypeSymbol type) implements Denotation {

        public Denotes {
            if (type == null) {
                throw new IllegalArgumentException("a name that denotes names a declaration");
            }
        }
    }

    /**
     * In scope and denoting nothing: a name an import line that could not do its job stands in for.
     *
     * <p>What is wrong was reported on that line, so a use of the name says nothing more — it takes
     * the error type and is read as a name nothing answered. This is the answer that is already
     * accounted for.
     */
    record StandsForNothing() implements Denotation {}

    /**
     * Nothing here is written that way.
     *
     * <p>Nobody has said anything about it yet, so the reader of the position is the one to report
     * it. This is the answer that still owes a diagnostic.
     */
    record NotInScope() implements Denotation {}

    Denotation STANDS_FOR_NOTHING = new StandsForNothing();

    Denotation NOT_IN_SCOPE = new NotInScope();

    /** The declaration this denotes, or null where it denotes none. For a reader that has one thing
     * to do with a declaration and nothing to do without one; a reader that tells the two absences
     * apart switches over this instead. */
    default TypeSymbol type() {
        return this instanceof Denotes d ? d.type() : null;
    }
}
