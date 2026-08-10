package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A member whose line is opened by something the enclosing block writes — a leading comma, a union's
 * {@code |}, the brace of a product body — is one line, and a comment written above it belongs above
 * that whole line. Decorating the member alone left the comment after the opener and dropped the
 * member itself to the nesting indent, so the block stopped being written in the form the rest of it
 * is written in.
 */
class ACommentSitsAboveTheWholeMemberLineTest {

    @Test
    void aboveAFieldThatOpensWithAComma() {
        String formatted = Formatter.format("""
                module m
                data D =
                    { a: Int
                    // the comment
                    , b: Int
                    }
                """);

        assertEquals("""
                module m

                data D =
                    { a: Int
                    // the comment
                    , b: Int
                    }
                """, formatted);
    }

    @Test
    void aboveTheFieldThatOpensWithTheBrace() {
        String formatted = Formatter.format("""
                module m
                data D =
                    {
                    // the comment
                      a: Int
                    , b: Int
                    }
                """);

        assertEquals("""
                module m

                data D =
                    // the comment
                    { a: Int
                    , b: Int
                    }
                """, formatted);
    }

    @Test
    void aboveACaseThatOpensWithABar() {
        String formatted = Formatter.format("""
                module m
                data A
                data B
                data S = A
                    // the comment
                    | B
                """);

        assertEquals("""
                module m

                data A
                data B
                data S = A
                    // the comment
                    | B
                """, formatted);
    }

    /** The comment is what breaks the union here: {@code data S = A | B} fits the canonical width,
     * and a {@code //} on a line the group had collapsed would swallow the case after it. */
    @Test
    void aCommentedUnionCannotBeWrittenFlat() {
        String formatted = Formatter.format("""
                module m
                data A
                data B
                data S =
                    // the comment
                    A | B
                """);

        assertEquals("""
                module m

                data A
                data B
                data S =
                    // the comment
                    A | B
                """, formatted);
    }
}
