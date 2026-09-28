package souther.compiler.regex;

/**
 * What came of reading a pattern.
 *
 * <p>Three answers, and they are about three different things. {@link Read} is a pattern of the
 * language, as what it means. {@link Refused} is text that is no pattern of the language, and says
 * what in it is not. {@link TooDeep} is a pattern the language has and this compiler does not read,
 * which is a limit of the compiler: an author told that their pattern is not in the language would
 * go looking for a construct when every construct in it is one the language has.
 *
 * <p>A pattern read in part is not an answer: a tree of the constructs that were understood accepts
 * a language the author did not write, and every reader downstream would be holding a set narrower
 * than the rule.
 */
public sealed interface PatternRead {

    /** The whole pattern, as the strings it accepts. */
    record Read(PatternMeaning meaning) implements PatternRead {

        public Read {
            if (meaning == null) {
                throw new IllegalArgumentException("a pattern that was read says what it accepts");
            }
        }
    }

    /**
     * Text that is no pattern of the language, and what stopped the reading.
     *
     * @param why       which kind of thing it is
     * @param from      where in the text the construct that stopped it begins, in chars
     * @param construct the construct as written, which is empty where the text ended before a
     *                  construct it had begun was whole
     */
    record Refused(Refusal why, int from, String construct) implements PatternRead {

        public Refused {
            if (why == null || construct == null || from < 0) {
                throw new IllegalArgumentException("a pattern refused was stopped by something");
            }
        }
    }

    /**
     * A pattern written more deeply than this compiler reads.
     *
     * <p>Not a refusal: the language has no depth past which a pattern stops being one. Every part
     * that works a pattern out — the reader, the machines built from it, what an output lowers it to —
     * walks it by its depth, and this is where the compiler says how deep it will go.
     *
     * @param deepest how deep a pattern may be written
     */
    record TooDeep(int deepest) implements PatternRead {}

    /**
     * What makes text no pattern of the language.
     *
     * <p>Told apart by what an author wrote. The first group is text that is no pattern at all —
     * something left open, a count or an escape with no meaning. The rest is text that would be a
     * pattern in some other language and is not one in this, each for a reason of its own (spec
     * §string-patterns): a back reference can denote a set no regular language is, a possessive
     * count's strings follow from how a matcher walks, a flag would change what a class means for
     * the rest of the pattern, and the others have no spelling in the grammar. Not "denotes no set
     * of strings": a lookahead often denotes one, and a regular one at that.
     */
    enum Refusal {

        /** A bracket, brace or parenthesis with nothing closing it, a class with nothing in it, or
         *  a repetition with nothing before it to repeat. */
        SOMETHING_UNCLOSED,

        /** A repetition whose count is no count: one with no digits, one too large to hold, a
         *  ceiling below its floor, or a run whose end comes before its start. */
        A_COUNT_THIS_CANNOT_READ,

        /** An escape with no meaning, or one with nothing after it. */
        AN_ESCAPE_THIS_DOES_NOT_READ,

        /**
         * An escape writing half of a surrogate pair — {@code \\uD800} on its own,
         * {@code \x{DC00}}.
         *
         * <p>No {@code String} holds such a character, so a pattern naming one says something about
         * text that never arrives.
         */
        A_CHARACTER_NO_STRING_HOLDS,

        /** A group beginning {@code (?} other than {@code (?:} — a lookahead, a lookbehind, a named
         *  group, a flag group. None has a spelling in the grammar, and a flag would change what a
         *  class means for the rest of the pattern. */
        A_GROUP_THE_GRAMMAR_DOES_NOT_HAVE,

        /** A reference back to what another part of the pattern matched, which can denote a set no
         *  regular language is. */
        A_BACK_REFERENCE,

        /** A property of a character — {@code \p{Alpha}}, {@code \P{...}}. The language names
         *  symbols by their numbers and has nothing to ask a property with. */
        A_CHARACTER_PROPERTY,

        /** A boundary — {@code \b}, {@code \B}, {@code \A}, {@code \z}, {@code \Z}, {@code \G},
         *  {@code \R}. The grammar has {@code ^} and {@code $} for the ends and nothing else that
         *  stands between characters. */
        A_BOUNDARY,

        /** A quotation — {@code \Q ... \E} — which turns off the reading of what is inside it. */
        A_QUOTATION,

        /** A class inside a class, or classes joined by {@code &&}. */
        A_CLASS_OF_CLASSES,

        /**
         * A repetition that gives nothing back.
         *
         * <p>{@code ++}, {@code *+} and the rest. Unlike a reluctant marker, which changes the
         * order a matcher tries things and not which strings come out, a possessive one takes what
         * it can and never tries again — so a body that accepts the empty string takes it once and
         * stops. Which strings it accepts follows from that walk, which the language does not
         * describe.
         */
        A_POSSESSIVE_REPETITION,

        /**
         * An anchor whose answer is not a property of the pattern.
         *
         * <p>{@code ^} and {@code $} are read where the shape says whether everything on that side
         * of them takes a symbol or nothing on that side does. {@code (a|)^b} is neither: which
         * strings it accepts is settled by which arm a string took, and the language has no shape
         * for a set written that way.
         */
        AN_ANCHOR_THIS_CANNOT_PLACE
    }
}
