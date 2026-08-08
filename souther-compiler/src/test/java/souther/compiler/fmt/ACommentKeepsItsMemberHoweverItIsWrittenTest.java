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

    /** One member written as several identifiers. A comment anywhere in the name is about the
     * whole name, so the two ends of the run have to agree on which member they are — reading each
     * identifier as a member of its own left the comment owned by something nobody asked for. */
    @Test
    void aMemberWrittenAsSeveralIdentifiers() {
        assertEquals("""
                module m

                data A =
                    { n: Int
                    }

                behavior f : (n: Int) -> A
                    // why this one
                    constructs other.A

                let f (n) = A { n = n }
                """, Formatter.format("""
                module m
                data A = { n: Int }
                behavior f : (n: Int) -> A
                    constructs other.
                        // why this one
                        A
                let f (n) = A { n = n }
                """));
    }

    /** Written as the tail of a header line: a behavior's return type, with clauses under it. The
     * clauses are the construct's next lines, so a comment ending the header's line is not a comment
     * about them. */
    @Test
    void aMemberWrittenAsTheTailOfAHeader() {
        assertEquals("""
                module m

                data A =
                    { n: Int
                    }

                behavior f : (n: Int) -> A // result
                    constructs A

                let f (n) = A { n = n }
                """, Formatter.format("""
                module m
                data A = { n: Int }
                behavior f : (n: Int) -> A   // result
                    constructs A
                let f (n) = A { n = n }
                """));
    }

    /** The same shape one construct down: what a newtype wraps, with an invariant under it. */
    @Test
    void andTheSameTailOnADataHeader() {
        assertEquals("""
                module m

                data Positive = Int // representation
                    invariant value > 0
                """, Formatter.format("""
                module m
                data Positive = Int   // representation
                    invariant value > 0
                """));
    }

    /** Written as a segment of a chain: a stage of a pipeline, and a member of a written union. */
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

    @Test
    void aMemberWrittenAsASegmentOfAWrittenUnion() {
        assertEquals("""
                module m

                data A =
                    { n: Int
                    }

                data B =
                    { n: Int
                    }

                behavior f : (n: Int) -> A
                    // exceptional result
                    | B

                let f (n) = A { n = n }
                """, Formatter.format("""
                module m
                data A = { n: Int }
                data B = { n: Int }
                behavior f : (n: Int) -> A
                    // exceptional result
                    | B
                let f (n) = A { n = n }
                """));
    }

    /**
     * Written as part of a run the layout flattens. The parser reads {@code 1 |> b |> c} as nesting
     * and the layout writes it as one run of segments, so what the comment is about — the inner
     * {@code 1 |> b} — is not a construct the output has a line for. Its segment is.
     */
    @Test
    void aMemberWrittenAsPartOfAFlattenedRun() {
        assertEquals("""
                module m

                let b (x: Int) = x

                let c (x: Int) = x

                let value =
                    1
                        |> b // about the b stage
                        |> c
                """, Formatter.format("""
                module m
                let b (x: Int) = x
                let c (x: Int) = x
                let value = 1
                    |> b   // about the b stage
                    |> c
                """));
    }

    /** An operator run is the same shape, and was the same defect: the segments are what the layout
     * writes, and only the pipeline had been asked. */
    @Test
    void andAnOperatorRunIsTheSameShape() {
        assertEquals("""
                module m

                let value =
                    1
                        + 2 // about the second term
                        + 3
                """, Formatter.format("""
                module m
                let value = 1
                    + 2   // about the second term
                    + 3
                """));
    }

    /** Written as a member of a nested bracketed construct: a type argument. It is a node, like a
     * field, and unlike a field it was not being read as a member. */
    @Test
    void aMemberWrittenInsideNestedBrackets() {
        assertEquals("""
                module m

                data D =
                    { xs: List<
                        // element type
                        Int
                    >
                    }
                """, Formatter.format("""
                module m
                data D =
                    { xs: List<
                        // element type
                        Int
                      >
                    }
                """));
    }

    /** The other side of an operator run: what is written above a segment rather than at the end of
     * one. The two are separate paths and only the first had been asked for. */
    @Test
    void andAboveASegmentOfAnOperatorRun() {
        assertEquals("""
                module m

                let value =
                    1
                        // about the second term
                        + 2
                        + 3
                """, Formatter.format("""
                module m
                let value = 1
                    // about the second term
                    + 2
                    + 3
                """));
    }

    /** Under the last member of a nested bracketed construct. What closes a type's arguments is the
     * same angle bracket the grammar compares with, so it had to be read as the closer it is here
     * before it was read as the operator it is elsewhere. */
    @Test
    void underTheLastMemberOfNestedBrackets() {
        assertEquals("""
                module m

                data D =
                    { xs: List<
                        Int
                        // why Int is allowed
                    >
                    }
                """, Formatter.format("""
                module m
                data D =
                    { xs: List<
                        Int
                        // why Int is allowed
                      >
                    }
                """));
    }

    /**
     * Written at the end of a line a construct opens with rather than the line it ends on. A
     * construct written over several lines has more lines than its last, and `data D =`,
     * `match x with` and the `{` of a block each end one of them. The whole construct's line was the
     * only one anything could be attached to, so a comment there came back after its last line.
     */
    @Test
    void aLineAConstructOpensWith() {
        assertEquals("""
                module m

                data D = // about the block
                    { a: Int
                    , b: Int
                    }
                """, Formatter.format("""
                module m
                data D =   // about the block
                    { a: Int
                    , b: Int
                    }
                """));
    }

    /**
     * Written about one part of a row, which the layout writes as a chain of segments the way it
     * writes a pipeline. A row's input and its expected value are segments, and so is a match arm's
     * body; none of the three was asked what was written about it, so all three answered with the
     * row or the arm.
     */
    @Test
    void aPartOfARowWrittenAsAChain() {
        assertEquals("""
                module m

                let helper (n: Int) = n

                example helper
                    | (2)
                        // expected result
                        -> 2
                """, Formatter.format("""
                module m
                let helper (n: Int) = n

                example helper
                    | (2) ->
                        // expected result
                        2
                """));
        assertEquals("""
                module m

                let helper (n: Int) = n

                example helper
                    | (2) // input
                        -> 2
                """, Formatter.format("""
                module m
                let helper (n: Int) = n

                example helper
                    | (2)   // input
                        -> 2
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
