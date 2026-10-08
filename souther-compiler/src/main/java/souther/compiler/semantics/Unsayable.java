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

    /** That every character of a string is whitespace — what a trimmed string is empty for, and
     *  what a string with no words is. A string is no container of characters a statement can be
     *  made of each of. */
    EVERY_CHARACTER_IS_WHITESPACE("every character of a string being whitespace"),

    /** That a value is one a map is keyed by. What an element of a map is is its value, so its keys
     *  are no container a statement can be made of each of. */
    A_KEY_OF_A_MAP("a value being a key of a map"),

    /** That a string is made up of copies of another. What a replacement leaves is empty for that,
     *  and a string is no container of parts. */
    MADE_UP_OF_COPIES_OF_A_TEXT("a string being made up of copies of another"),

    /** That one string stands inside another, at its start or its end or anywhere. A string is
     *  no container of parts a statement can be made of. */
    A_STRING_INSIDE_ANOTHER("one string standing inside another"),

    /** That a string matches a pattern, which says something of every way the string could be
     *  taken apart. */
    A_STRING_MATCHING_A_PATTERN("a string matching a pattern"),

    /** That no two elements of a container come to one key. A statement about some element is
     *  about one element at a time, and this is about every pair of them. */
    NO_TWO_ELEMENTS_ALIKE("no two elements of a container coming to one key");

    private final String proposition;

    Unsayable(String proposition) {
        this.proposition = proposition;
    }

    /** The proposition the domain has no words for, as a report names it. */
    public String proposition() {
        return proposition;
    }
}
