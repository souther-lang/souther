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
    NO_TWO_ELEMENTS_ALIKE("no two elements of a container coming to one key"),

    /** How many different values a list holds — what a set made of it holds as many of. A count is
     *  of the elements meeting a statement about each of them, and whether two are one value is
     *  about a pair of them. */
    HOW_MANY_DIFFERENT_VALUES("how many different values a list holds");

    private final String proposition;

    Unsayable(String proposition) {
        this.proposition = proposition;
    }

    /**
     * Whether a body that comes to {@code reached} comes to this proposition for want of the same
     * words: the proposition itself, or one this is stated through. That no two elements are alike
     * is a set of them holding as many as the list does, so it wants the words a count of
     * different values wants.
     */
    public boolean standsOn(Unsayable reached) {
        return switch (this) {
            case NO_TWO_ELEMENTS_ALIKE -> reached == this || reached == HOW_MANY_DIFFERENT_VALUES;
            case EVERY_CHARACTER_IS_WHITESPACE, MADE_UP_OF_COPIES_OF_A_TEXT,
                 A_STRING_INSIDE_ANOTHER, A_STRING_MATCHING_A_PATTERN, HOW_MANY_DIFFERENT_VALUES ->
                    reached == this;
        };
    }

    /**
     * Whether what this says of a container, where it is about one, holds of what a construction
     * of {@code shape} builds of that container wherever it held of the container itself.
     *
     * <p>That no two elements are alike is about which elements a container holds and how many
     * times, so the same elements in another order have it, and so does any part of them, since a
     * pair alike among a part was a pair alike in the whole. Nothing else here is about a
     * container's elements at all.
     */
    public boolean survives(ElementShape shape) {
        return switch (this) {
            case NO_TWO_ELEMENTS_ALIKE -> switch (shape) {
                case PERMUTES, SUBSET -> true;
                case MAPS, COLLAPSES -> false;
            };
            case EVERY_CHARACTER_IS_WHITESPACE, MADE_UP_OF_COPIES_OF_A_TEXT,
                 A_STRING_INSIDE_ANOTHER, A_STRING_MATCHING_A_PATTERN, HOW_MANY_DIFFERENT_VALUES ->
                    false;
        };
    }

    /** The proposition the domain has no words for, as a report names it. */
    public String proposition() {
        return proposition;
    }
}
