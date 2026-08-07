package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comment stays on the member it was written about, whichever way the grammar writes that member.
 *
 * <p>The cases here are the ways a member can be written rather than the constructs that have
 * members: a member is a node, or a bare identifier the enclosing construct holds directly, or a
 * segment of a chain, or absent because the construct is empty, or a part of an expression with no
 * line of its own. A sum's cases needed their own answer because they are identifiers, and the
 * answer was written for sums alone — which left an import's names and a {@code constructs} clause's
 * names, the same way of writing a member under a different construct, still losing theirs.
 *
 * <p>The survival sweep cannot ask this. A comment moved from one member to the next is one comment
 * in and one comment out, and the code around it is unchanged; what changed is the only thing a
 * comment is for.
 */
class ACommentKeepsItsMemberHoweverItIsWrittenTest {

    /** Written as a node: a field of a product block. */
    @Test
    void aMemberWrittenAsANode() {
        assertEquals("""
                module m

                data D =
                    { a: Int
                    // about b
                    , b: Int
                    }
                """, Formatter.format("""
                module m
                data D =
                    { a: Int
                    // about b
                    , b: Int
                    }
                """));
    }

    /** Written as an identifier the construct holds directly: the names an import lists. */
    @Test
    void aMemberWrittenAsAnIdentifier() {
        assertEquals("""
                module m
                import other.mod (
                    A,
                    // about B
                    B
                )

                data O =
                    { n: Int
                    }
                """, Formatter.format("""
                module m
                import other.mod (
                    A,
                    // about B
                    B
                )
                data O = { n: Int }
                """));
    }

    /** The same way of writing a member, under a construct that is not a list of names. */
    @Test
    void aMemberWrittenAsAnIdentifierOfAClause() {
        assertEquals("""
                module m

                data A =
                    { n: Int
                    }

                data B =
                    { n: Int
                    }

                behavior f : (n: Int) -> A | B
                    constructs A,
                        // about B
                        B

                let f (n) = A { n = n }
                """, Formatter.format("""
                module m
                data A = { n: Int }
                data B = { n: Int }
                behavior f : (n: Int) -> A | B
                    constructs A,
                    // about B
                    B
                let f (n) = A { n = n }
                """));
    }

    /** Written as a segment of a chain: a stage of a pipeline. */
    @Test
    void aMemberWrittenAsASegmentOfAChain() {
        assertEquals("""
                module m

                data O =
                    { n: Int
                    }

                let g (x: Int) = x

                let h (x: Int) = x

                behavior f : (n: Int) -> O
                    constructs O

                let f (n) =
                    O {
                        n = n
                            |> g
                            // about h
                            |> h
                    }
                """, Formatter.format("""
                module m
                data O = { n: Int }
                let g (x: Int) = x
                let h (x: Int) = x
                behavior f : (n: Int) -> O constructs O
                let f (n) = O { n = n
                    |> g
                    // about h
                    |> h }
                """));
    }

    /** No member to be about: the comment was written above the construct, and stays above it rather
     * than moving inside where the construct's own end comments go. */
    @Test
    void aConstructWithNoMemberToBeAbout() {
        assertEquals("""
                module m

                data O =
                    { xs: List<Int>
                    }

                behavior f : () -> O
                    constructs O

                let f =
                    O {
                        // empty for now
                        xs = []
                    }
                """, Formatter.format("""
                module m
                data O = { xs: List<Int> }
                behavior f : () -> O constructs O
                let f = O { xs =
                    // empty for now
                    [] }
                """));
    }

    /** Written as part of an expression, which has no line of its own. The comment goes to the end
     * of the line the construct holding it ends, which is further than it was written and is what
     * keeps it out of the middle of a line. */
    @Test
    void aPartOfAnExpressionWithNoLineOfItsOwn() {
        assertEquals("""
                module m

                data One

                data Two

                let value (n: Int) = if n > 0 then One else Two // about the test
                """, Formatter.format("""
                module m
                data One
                data Two
                let value (n: Int) = if n > 0   // about the test
                    then One else Two
                """));
    }
}
