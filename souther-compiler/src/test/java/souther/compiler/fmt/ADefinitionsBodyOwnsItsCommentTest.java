package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A comment written above what a definition or an {@code if} writes after its keyword stays there.
 * The construct is given a line by the layout — the boundary before it breaks where the body does
 * not fit — and a comment is about what it was written above whether or not the width would have
 * kept that on one line. Owning one is then what puts it on a line of its own, since a comment
 * cannot share the line after it.
 *
 * <p>{@link ACommentKeepsItsMemberHoweverItIsWrittenTest} sweeps the ways a member can be written,
 * and the survival sweep cannot ask either of them: a comment handed to the enclosing construct is
 * one comment in and one comment out, and only which construct it is about has changed.
 */
class ADefinitionsBodyOwnsItsCommentTest {

    @Test
    void aDefinitionsBody() {
        assertEquals("""
                module m

                let g (x: Int): Int =
                    // about the body
                    x
                """, Formatter.format("""
                module m
                let g (x: Int): Int =
                    // about the body
                    x
                """));
    }

    @Test
    void aBranchOfAnIf() {
        assertEquals("""
                module m

                let k (x: Int): Int =
                    if x > 0 then
                        // about the then branch
                        1
                    else
                        0
                """, Formatter.format("""
                module m
                let k (x: Int): Int =
                    if x > 0 then
                        // about the then branch
                        1
                    else
                        0
                """));
    }

    @Test
    void andItsOtherBranch() {
        assertEquals("""
                module m

                let k (x: Int): Int =
                    if x > 0 then
                        1
                    else
                        // about the else branch
                        0
                """, Formatter.format("""
                module m
                let k (x: Int): Int =
                    if x > 0 then
                        1
                    else
                        // about the else branch
                        0
                """));
    }

    /**
     * And what an {@code if} writes on its header line owns nothing. The condition stands between
     * {@code if} and {@code then} with no boundary the layout can break, so a comment above it is a
     * comment about the {@code if} — which is why holding children is not what makes a construct
     * able to carry one.
     */
    @Test
    void butNotWhatTheHeaderLineHolds() {
        assertEquals("""
                module m

                let k (x: Int): Int =
                    // about the test
                    if x > 0 then 1 else 0
                """, Formatter.format("""
                module m
                let k (x: Int): Int =
                    if
                        // about the test
                        x > 0
                    then 1 else 0
                """));
    }

    /**
     * A definition written as a lambda is left as it was. Its parameters move to the left of the
     * {@code =}, so what the canonical form writes after the {@code =} is not the child the source
     * has there — it is that child's body, a level further down. The comment is about that body and
     * the construct the source gives it to is the lambda, and until the two are the same question
     * this is one construct where the comment still travels to the declaration.
     *
     * <p>Held here so that it is a stated limit rather than a case nobody tried. Making it right
     * needs the canonical structure to be something a comment can be filed against, which is
     * issue #444.
     */
    @Test
    void butADefinitionWrittenAsALambdaIsLeftAsItWas() {
        assertEquals("""
                module m

                // about the body
                let f (x) = x
                """, Formatter.format("""
                module m
                let f = (x) ->
                    // about the body
                    x
                """));
    }
}
