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
 * <p>The three used to be a {@link TypeName} that was null, a {@link TypeName} of a module no
 * source may name ({@code souther.unresolved}), and a {@link TypeName} — so a reader that took the
 * answer for a declaration was reading a fabricated identity, and eight of them asked
 * {@code isUnresolved()} afterwards to find out. An answer that has to be asked what it is is an
 * answer a reader can forget to ask.
 */
public sealed interface Denotation {

    /** The declaration the name denotes here. */
    record Denotes(TypeName type) implements Denotation {

        public Denotes {
            if (type == null) {
                throw new IllegalArgumentException("a name that denotes names a declaration");
            }
        }
    }

    /** In scope, denoting nothing — a name a failed import line stands in for. */
    record Nothing() implements Denotation {}

    /** Nothing here is written that way. */
    record Unknown() implements Denotation {}

    Denotation NOTHING = new Nothing();

    Denotation UNKNOWN = new Unknown();

    /** The declaration this denotes, or null where it denotes none. For a reader that has one thing
     * to do with a declaration and nothing to do without one; a reader that tells the two absences
     * apart switches over this instead. */
    default TypeName type() {
        return this instanceof Denotes d ? d.type() : null;
    }
}
