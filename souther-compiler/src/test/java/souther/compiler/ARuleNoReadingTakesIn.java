package souther.compiler;

/**
 * A rule about one string that no reading of this compiler's takes in, for tests that need one.
 *
 * <p>Written here and not at each of them. What a test wanting this needs is the <em>property</em> —
 * a clause an author may write, about a position a reader can name, that arrives at the readings as
 * a form none of them has a word for. Which spelling has that property is a fact about what this
 * compiler reads today, and it moves: {@code String.startsWith} had it until the reading of string
 * predicates learned what such a call says about a position, and eight test files that had each
 * written that call out went quiet about what they were for on the same day (issue #1249).
 *
 * <p>So the spelling is one line, and {@link ARuleNoReadingTakesInIsStillOneTest} is what holds the
 * property to it. The next capability that takes this clause in fails that one test, which says
 * exactly what has happened — the examples below need a new spelling — rather than leaving eight
 * files asserting things about a rule that is now read.
 *
 * <p>Not a promise that this can never be read. Anything an author writes may be read one day, and
 * what this is for is making the day it happens loud.
 */
public final class ARuleNoReadingTakesIn {

    private ARuleNoReadingTakesIn() {}

    /**
     * The clause, about whatever {@code subject} names.
     *
     * <p>Wide on purpose: it holds of every string but the empty one, so a model that carries rows
     * keeps them, and what a test is measuring is the reading rather than a value it had to go and
     * change. A clause admitting one value would make every row beside it about the clause.
     */
    public static String about(String subject) {
        return "String.reverse(" + subject + ") /= \"\"";
    }

    /** A value it admits, where a row has to carry one. */
    public static final String A_VALUE_IT_ADMITS = "\"x\"";
}
