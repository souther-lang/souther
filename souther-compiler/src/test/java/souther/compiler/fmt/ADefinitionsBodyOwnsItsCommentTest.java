package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

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
     * And so does one written as a lambda. Its parameters move to the left of the {@code =}, so what
     * the canonical form writes after the {@code =} is not the child the source has there — it is
     * that child's body, a level further down. The comment is about that body, and the body is a
     * place of the canonical form whether or not the source has a construct in that position.
     */
    @Test
    void andSoDoesOneWrittenAsALambda() {
        assertEquals("""
                module m

                let f (x) =
                    // about the body
                    x
                """, Formatter.format("""
                module m
                let f = (x) ->
                    // about the body
                    x
                """));
    }

    /** A lambda whose body is another lambda lifts the outer one only, so what is written after the
     * {@code =} is the inner lambda and the comment is above all of it. */
    @Test
    void andOneWhoseBodyIsAnotherLambda() {
        assertEquals("""
                module m

                let g (x) =
                    // about the body
                    (y) -> x
                """, Formatter.format("""
                module m
                let g = (x) ->
                    // about the body
                    (y) -> x
                """));
    }

    /**
     * And the place that carries it is the body's.
     *
     * <p>Read from the text alone this case cannot be told from the one it used to be: a comment
     * carried by the declaration is written on the line before the body too, and the count of
     * comments is the same either way. What has to be true is that the place handed the comment is
     * the one the lambda's last expression child was written at — which is not the place the source
     * has a construct at, and is why asking the source tree a second time answered wrongly here.
     */
    @Test
    void andTheCarrierIsTheBodysPlaceAndNotTheDefinitions() {
        SyntaxNode root = CstParser.parse("""
                module m
                let f = (x) ->
                    // about the body
                    x
                """).root();
        Formatter.Construction built = Formatter.build(root);

        SyntaxNode lambda = only(root, SyntaxKind.LAMBDA_EXPR);
        SyntaxNode body = childOf(lambda, SyntaxKind.VAR_EXPR);
        Place carrier = carrierOf(built, Carrier.ABOVE);

        assertEquals(List.of(new Written.Construct(body)), built.places().sourcesOf(carrier),
                "the comment is carried by the place the lambda's body was written at");
        assertNotSame(carrier, built.places().placesOf(new Written.Construct(lambda.parent())).get(0),
                "and not by the definition's own place, which is where it used to travel to");
        assertTrue(built.places().sourcesOf(carrier.parent())
                        .contains(new Written.Construct(lambda.parent())),
                "the carrier is one of the definition's places: " + carrier.parent());
    }

    /** The one place a comment was handed in that direction. */
    private static Place carrierOf(Formatter.Construction built, Carrier which) {
        List<Place> found = new ArrayList<>();
        for (var e : built.carriers().entrySet()) {
            if (!e.getValue().getOrDefault(which, List.of()).isEmpty()) {
                found.add(e.getKey());
            }
        }
        assertEquals(1, found.size(), "one place carries the fixture's one comment: " + found);
        return found.get(0);
    }

    private static SyntaxNode only(SyntaxNode from, SyntaxKind kind) {
        List<SyntaxNode> out = new ArrayList<>();
        descend(from, kind, out);
        assertEquals(1, out.size(), "the fixture writes one " + kind);
        return out.get(0);
    }

    private static void descend(SyntaxNode n, SyntaxKind kind, List<SyntaxNode> out) {
        if (n.kind() == kind) {
            out.add(n);
        }
        for (SyntaxNode c : n.childNodes()) {
            descend(c, kind, out);
        }
    }

    private static SyntaxNode childOf(SyntaxNode n, SyntaxKind kind) {
        return n.child(kind).orElseThrow();
    }
}
