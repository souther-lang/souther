package souther.compiler.regex;

/**
 * What came of reading a pattern's syntax.
 *
 * <p>Two answers and no third. Either the whole of the pattern is in the subset this reads, and what
 * comes back says which strings it accepts; or something in it is not, and what comes back says
 * which kind of thing that was. A pattern read in part is not an answer: a tree of the constructs
 * that were understood accepts a language the author did not write, and every reader downstream
 * would be holding a set narrower than the rule.
 */
public sealed interface PatternRead {

    /** The whole pattern, as the strings it accepts. */
    record Read(PatternSyntax syntax) implements PatternRead {

        public Read {
            if (syntax == null) {
                throw new IllegalArgumentException("a pattern that was read says what it accepts");
            }
        }
    }

    /** Something in it this does not read, and which kind of thing. */
    record NotRead(Unsupported why) implements PatternRead {

        public NotRead {
            if (why == null) {
                throw new IllegalArgumentException("a pattern nothing read was stopped by something");
            }
        }
    }

    /**
     * Which construct stopped the reading.
     *
     * <p>Told apart by what an author wrote rather than by what this compiler would have to gain.
     * Which of these is worth reading one day is a question about the words in front of somebody,
     * and a reason saying only that something was unsupported answers none of it.
     *
     * <p>Not a promise to anyone outside. What a document writes for a rule this could not read is
     * one word, said where a document is written; these are for the reading that produced them and
     * for whoever comes to widen the subset.
     */
    enum Unsupported {

        /** A group that says something about the match rather than about the strings — a lookahead,
         *  a lookbehind, a named or capturing-by-name group, a flag group. */
        A_GROUP_ABOUT_THE_MATCH,

        /** A reference back to what another part of the pattern matched, which no set of strings
         *  states. */
        A_BACK_REFERENCE,

        /** A property of a character rather than a run of them — `\p{Alpha}`, `\P{...}`. The subset
         *  here names symbols by their numbers and has nothing to ask a property with. */
        A_CHARACTER_PROPERTY,

        /** A boundary — `\b`, `\B`, `\A`, `\z`, `\Z`, `\G`. It is about where a match sits in the
         *  input, and the whole of the input is what is matched here. */
        A_BOUNDARY,

        /** A quotation — `\Q ... \E` — which turns off the reading of what is inside it. */
        A_QUOTATION,

        /** Classes joined by `&&`, which is an operation over classes this does not read. */
        A_CLASS_OF_CLASSES,

        /** A repetition of more than this reads: a count with no digits, or one past what a whole
         *  number holds. */
        A_COUNT_THIS_CANNOT_READ,

        /** A bracket, brace or parenthesis with nothing closing it, or a class with nothing in it. */
        SOMETHING_UNCLOSED,

        /** An escape this has no meaning for, or one with nothing after it. */
        AN_ESCAPE_THIS_DOES_NOT_READ,

        /**
         * An anchor whose answer is not a property of the pattern.
         *
         * <p>{@code ^} and {@code $} are read where the shape says whether everything on that side
         * of them takes a symbol or nothing on that side does. {@code (a|)^b} is neither: which
         * strings it accepts is settled by which arm a string took, and this compiler has no shape
         * for a language written that way. So the pattern is not read, rather than read as one of
         * the two answers it is not.
         */
        AN_ANCHOR_THIS_CANNOT_PLACE,

        /** Written more deeply than this reads, which is a limit of the reading and not of the
         *  language. */
        NESTED_TOO_DEEPLY
    }
}
