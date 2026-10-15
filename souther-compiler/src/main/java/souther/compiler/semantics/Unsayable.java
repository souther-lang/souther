package souther.compiler.semantics;

/**
 * A proposition an observation of an operation's answer comes to, which a statement over the
 * arguments has no words for ({@link LawProposition}).
 *
 * <p>Why an observation is closed rather than given a law. What it names is known; it is the
 * domain that cannot say it, so a reading that meets one stops on a fact about the domain and not
 * on a law nobody wrote. Each is named by the proposition and not by the operation, since two
 * operations that come to one proposition stop for one reason.
 */
public enum Unsayable {

    /** That a string is made up of copies of another. What a replacement leaves is empty for that,
     *  and a string is no container of parts. */
    MADE_UP_OF_COPIES_OF_A_TEXT("a string being made up of copies of another"),

    /** That one string stands inside another, at its start or its end or anywhere. A string is
     *  no container of parts a statement can be made of. */
    A_STRING_INSIDE_ANOTHER("one string standing inside another"),

    /** That a string matches a pattern, which says something of every way the string could be
     *  taken apart. */
    A_STRING_MATCHING_A_PATTERN("a string matching a pattern"),

    /** Which characters of a string are whitespace — how many a trimmed string loses at its ends,
     *  and how many words whitespace parts a string into. A string is no container of characters
     *  a statement can be made of each of. */
    WHICH_CHARACTERS_ARE_WHITESPACE("which characters of a string are whitespace"),

    /** How many times one string stands inside another — how many pieces a separator parts a
     *  string into, and how many places a replacement is made at. */
    HOW_MANY_TIMES_A_STRING_STANDS_INSIDE_ANOTHER("how many times one string stands inside another"),

    /** How many code points a text holds once it is written in its canonical form, or its case is
     *  changed: a mark can join the letter before it, which can then take a mark it already had,
     *  and one letter can change case into several. What a text is put together from or rewritten
     *  into is in that form, so how long it is no number of the texts it came from says. */
    THE_LENGTH_OF_A_REWRITTEN_TEXT("how many code points a text holds once it is put in its"
            + " canonical form or its case is changed"),

    /** How many characters a number is written out in. */
    HOW_MANY_CHARACTERS_A_NUMBER_IS_WRITTEN_IN("how many characters a number is written out in");

    private final String proposition;

    Unsayable(String proposition) {
        this.proposition = proposition;
    }

    /** The proposition the domain has no words for, as a report names it. */
    public String proposition() {
        return proposition;
    }
}
