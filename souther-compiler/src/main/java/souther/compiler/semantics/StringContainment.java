package souther.compiler.semantics;

/**
 * Where in a string another stands, for the operations that ask whether one string is inside
 * another.
 *
 * <p>The three of them say one thing about two strings and differ in where the inner one is
 * looked for, so they are one relation with a place and not three relations. A statement that the
 * inner string is at the start is the statement that it is anywhere, with the place narrowed.
 */
public enum StringContainment {

    /** {@code String.contains}: the inner string stands somewhere in the other. */
    ANYWHERE,

    /** {@code String.startsWith}: the inner string is the beginning of the other. */
    AT_THE_START,

    /** {@code String.endsWith}: the inner string is the end of the other. */
    AT_THE_END;

    /** Whether {@code inner} stands where this says in {@code outer}. */
    public boolean holds(String inner, String outer) {
        return switch (this) {
            case ANYWHERE -> outer.contains(inner);
            case AT_THE_START -> outer.startsWith(inner);
            case AT_THE_END -> outer.endsWith(inner);
        };
    }
}
