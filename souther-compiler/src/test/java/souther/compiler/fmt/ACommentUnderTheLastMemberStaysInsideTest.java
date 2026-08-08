package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comment written under a construct's last member was written inside that construct, and comes
 * back inside it. It is above no member, so a walk that hands a run of comments to the next member
 * it meets never hands this one to anybody; and a construct with no members at all has nothing to
 * hand it to and still has somewhere to put it, which is between its brackets.
 *
 * <p>Two comments on consecutive lines stay two comments. Writing the one that ends a member's line
 * after the one written under it puts the second inside the first, which reads back as one comment
 * and is a comment lost — through a check that counts what was consumed rather than what was
 * written.
 */
class ACommentUnderTheLastMemberStaysInsideTest {

    @Test
    void underTheLastMemberOfAnEmptyList() {
        String formatted = Formatter.format("""
                module m exposing (
                    // keep me
                )
                data O = { n: Int }
                """);

        assertEquals("""
                module m exposing (
                    // keep me
                )

                data O =
                    { n: Int
                    }
                """, formatted);
    }

    @Test
    void underTheLastMemberOfAnEmptyRecordLiteral() {
        String formatted = Formatter.format("""
                module m
                data O
                behavior f : () -> O constructs O
                let f = O {
                    // keep me
                }
                """);

        assertEquals("""
                module m

                data O

                behavior f : () -> O
                    constructs O

                let f =
                    O {
                        // keep me
                    }
                """, formatted);
    }

    @Test
    void besideTheLastMemberAndUnderItAtOnce() {
        String formatted = Formatter.format("""
                module m
                data O = { a: Int, b: Int }
                behavior f : (n: Int) -> O constructs O
                let f (n) = O {
                    a = n,
                    b = n   // about b
                    // before close
                }
                """);

        assertEquals("""
                module m

                data O =
                    { a: Int
                    , b: Int
                    }

                behavior f : (n: Int) -> O
                    constructs O

                let f (n) =
                    O {
                        a = n,
                        b = n // about b
                        // before close
                    }
                """, formatted);
    }
}
