package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The canonical form has places of its own, and they are kept.
 *
 * <p>The formatter used to build them and keep neither them nor what the source had at each, so
 * anything asked afterwards — which construct can carry a comment, which one a rule is about — was
 * answered by walking the source tree again. Where the two structures differ that walk answers about
 * a construct the canonical form does not write, and a definition written as a lambda is where they
 * differ: its parameters move to the left of the {@code =}, and what is written after the {@code =}
 * is the lambda's body rather than the child the source has there.
 */
class ThePlacesTheCanonicalFormWritesAreItsOwnTest {

    /**
     * Written {@code if flag then p else q} an {@code if}'s three children are all a
     * {@code VAR_EXPR}, so the kind does not tell them apart. Which of its parent's places each one
     * is, does.
     */
    @Test
    void twoChildrenWrittenAsTheSameKindOfConstructAreTwoPlaces() {
        Correspondence places = placesOf("""
                module m
                let k (flag: Bool, p: Int, q: Int): Int =
                    if flag then p else q
                """);
        List<SyntaxNode> written = childrenOf(only(SyntaxKind.IF_EXPR), SyntaxKind.VAR_EXPR);

        List<Place> at = new ArrayList<>();
        for (SyntaxNode c : written) {
            List<Place> of = places.placesOf(new Written.Construct(c));
            assertEquals(1, of.size(), "one place is written for " + c);
            at.add(of.get(0));
        }

        assertEquals(3, at.size(), "a condition, a then branch and an else branch");
        assertNotSame(at.get(0), at.get(1));
        assertNotSame(at.get(1), at.get(2));
        assertNotSame(at.get(0), at.get(2));
        assertEquals(List.of(SyntaxKind.VAR_EXPR, SyntaxKind.VAR_EXPR, SyntaxKind.VAR_EXPR),
                at.stream().map(Place::construct).toList(),
                "and the kind is the same for all three, which is why it cannot tell them apart");
    }

    /** Each of them can say which place it is written under, and which of that place's it is. */
    @Test
    void andEachOfThemSaysWhoseAndWhichItIs() {
        Correspondence places = placesOf("""
                module m
                let k (flag: Bool, p: Int, q: Int): Int =
                    if flag then p else q
                """);
        List<SyntaxNode> written = childrenOf(only(SyntaxKind.IF_EXPR), SyntaxKind.VAR_EXPR);
        Place condition = places.placesOf(new Written.Construct(written.get(0))).get(0);
        Place then = places.placesOf(new Written.Construct(written.get(1))).get(0);
        Place otherwise = places.placesOf(new Written.Construct(written.get(2))).get(0);

        assertSame(condition.parent(), then.parent(), "all three are under the `if`");
        assertSame(then.parent(), otherwise.parent());
        assertEquals(List.of(0, 1, 2),
                List.of(condition.ordinal(), then.ordinal(), otherwise.ordinal()),
                "counted in the order they are written");
    }

    /**
     * A place is not another name for a source node. The definition below is written back as
     * {@code let f (x) = x}, and the parameter list there is a place the source tree has no node at:
     * what the source has in that position is the lambda, which the canonical form writes nowhere.
     */
    @Test
    void oneSourceElementStandsBehindOnePlaceAndItsDescendantBehindAnother() {
        Correspondence places = placesOf("""
                module m
                let f = (x) -> x
                """);
        SyntaxNode lambda = only(SyntaxKind.LAMBDA_EXPR);
        SyntaxNode body = childrenOf(lambda, SyntaxKind.VAR_EXPR).get(0);

        List<Place> ofTheLambda = places.placesOf(new Written.Construct(lambda));
        List<Place> ofTheBody = places.placesOf(new Written.Construct(body));

        assertEquals(SyntaxKind.FN_PARAM_LIST, ofTheLambda.get(0).construct(),
                "the lambda supplies the parameter list the definition writes on the left of `=`");
        assertEquals(SyntaxKind.VAR_EXPR, ofTheBody.get(0).construct(),
                "and its last expression child supplies what is written after the `=`");
        assertSame(ofTheLambda.get(0).parent(), ofTheBody.get(0).parent(),
                "both are places of the definition, which is what the canonical form writes here");
    }

    /**
     * And the relation is not one-to-one in either direction. Nothing may read it as if it were:
     * asking a place for <em>the</em> source element it came from is the question that has no
     * answer here.
     */
    @Test
    void andOneSourceElementMayStandBehindMoreThanOnePlace() {
        Correspondence places = placesOf("""
                module m
                let g = (x) -> (y) -> x
                """);
        List<SyntaxNode> lambdas = allOf(SyntaxKind.LAMBDA_EXPR);
        SyntaxNode inner = lambdas.get(1);

        List<Place> of = places.placesOf(new Written.Construct(inner));

        assertTrue(of.size() > 1,
                "the inner lambda is both what the outer one's body place holds and a construct"
                        + " with places of its own, and it is written at both: " + of);
    }

    /**
     * A place the source has nothing at is ordinary. A {@code fake}'s default row is written
     * {@code | _ -> …}, and the {@code _} is the canonical form's own: the source wrote no input
     * there at all.
     */
    @Test
    void andAPlaceMayStandForNothingTheSourceWrote() {
        Formatter.Construction built = Formatter.build(CstParser.parse("""
                module m
                data R =
                    { x: Int
                    }

                behavior f : () -> R
                    constructs R

                fake f
                    | _ -> R { x = 0 }
                """).root());

        List<Place> empty = new ArrayList<>();
        for (Place p : placesIn(built.doc())) {
            if (built.places().sourcesOf(p).isEmpty()) {
                empty.add(p);
            }
        }

        assertTrue(!empty.isEmpty(),
                "the default row's input is a place the source has nothing at");
    }

    // --- reading the tree ---
    //
    // One parse per fixture, and every lookup goes through that one root. A place says which source
    // element it was written from by holding the element itself, and the tree hands back one node
    // per position — so a second parse of the same text is a different tree, and nothing written
    // from the first is found in it.

    private SyntaxNode root;

    private Correspondence placesOf(String src) {
        root = CstParser.parse(src).root();
        return Formatter.placesOf(root);
    }

    private SyntaxNode only(SyntaxKind kind) {
        List<SyntaxNode> found = allOf(kind);
        assertEquals(1, found.size(), "the fixture writes one " + kind);
        return found.get(0);
    }

    private List<SyntaxNode> allOf(SyntaxKind kind) {
        List<SyntaxNode> out = new ArrayList<>();
        descend(root, kind, out);
        return out;
    }

    private static void descend(SyntaxNode n, SyntaxKind kind, List<SyntaxNode> out) {
        if (n.kind() == kind) {
            out.add(n);
        }
        for (SyntaxNode c : n.childNodes()) {
            descend(c, kind, out);
        }
    }

    private static List<SyntaxNode> childrenOf(SyntaxNode n, SyntaxKind kind) {
        List<SyntaxNode> out = new ArrayList<>();
        for (SyntaxNode c : n.childNodes()) {
            if (c.kind() == kind) {
                out.add(c);
            }
        }
        return out;
    }

    private static List<Place> placesIn(TokenDoc doc) {
        List<Place> out = new ArrayList<>();
        collect(doc, out);
        return out;
    }

    private static void collect(TokenDoc doc, List<Place> out) {
        switch (doc) {
            case TokenDoc.At a -> {
                out.add(a.place());
                collect(a.doc(), out);
            }
            case TokenDoc.Node n -> collect(n.doc(), out);
            case TokenDoc.Nest n -> collect(n.doc(), out);
            case TokenDoc.Group g -> collect(g.doc(), out);
            case TokenDoc.Concat c -> c.parts().forEach(part -> collect(part, out));
            case TokenDoc.Nil _, TokenDoc.Token _, TokenDoc.Comment _, TokenDoc.Trailing _,
                    TokenDoc.Gap _, TokenDoc.MustBreak _ -> { }
            case TokenDoc.Carries c -> throw new IllegalStateException(
                    "a carrier survived the resolution: " + c);
            case TokenDoc.Vacant v -> throw new IllegalStateException(
                    "brackets survived the resolution unfilled: " + v);
        }
    }
}
