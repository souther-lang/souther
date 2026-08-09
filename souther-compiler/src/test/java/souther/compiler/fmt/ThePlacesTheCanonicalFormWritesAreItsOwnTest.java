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
        Formatter.Construction built = build("""
                module m
                let k (flag: Bool, p: Int, q: Int): Int =
                    if flag then p else q
                """);
        List<SyntaxNode> written = childrenOf(only(SyntaxKind.IF_EXPR), SyntaxKind.VAR_EXPR);
        Place condition = built.places().placesOf(new Written.Construct(written.get(0))).get(0);
        Place then = built.places().placesOf(new Written.Construct(written.get(1))).get(0);
        Place otherwise = built.places().placesOf(new Written.Construct(written.get(2))).get(0);

        assertSame(condition.parent(), then.parent(), "all three are under the `if`");
        assertSame(then.parent(), otherwise.parent());
        assertEquals(List.of(0, 1, 2), List.of(built.order().get(condition),
                        built.order().get(then), built.order().get(otherwise)),
                "counted in the order they are written");
    }

    /**
     * And it is counted in the order the document writes them, not the order the formatter made
     * them.
     *
     * <p>A declaration builds its {@code invariant} clauses before its body and writes the body
     * first; an {@code example} builds its rows before the line it opens with and writes that line
     * first. Counted as they are made, both come back reversed — which is the formatter's
     * evaluation order recorded as a fact about the canonical form.
     */
    @Test
    void andItIsCountedInTheOrderTheDocumentWritesThem() {
        Formatter.Construction built = build("""
                module m
                data Amount = Int
                    invariant value > 0
                """);
        SyntaxNode data = only(SyntaxKind.DATA_DEF);
        Place body = built.places()
                .placesOf(new Written.Construct(childOf(data, SyntaxKind.NEWTYPE_BODY))).get(0);
        Place invariant = built.places()
                .placesOf(new Written.Construct(childOf(data, SyntaxKind.INVARIANT_CLAUSE))).get(0);

        assertSame(body.parent(), invariant.parent(), "both are places of the declaration");
        assertTrue(built.order().get(body) < built.order().get(invariant),
                "the body is written on the declaration's line and the clause below it, so the body"
                        + " is the earlier of the two: " + built.order().get(body) + " and "
                        + built.order().get(invariant));
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

    /**
     * And every construct of the source has one answer or the other.
     *
     * <p>This is what lets the walk that finds a carrier stay on the places. Where a construct had
     * no answer the walk went to the source tree for one — up to the construct holding it, and then
     * to that construct's first or last child, which is a guess about where the canonical form put
     * it. The construction is not guessing: it knows which place it wrote each construct at as it
     * writes it, and a construct it recorded nothing for is a hole this fails on rather than a case
     * the walk quietly covers.
     */
    @Test
    void andEveryConstructOfTheSourceIsWrittenSomewhere() {
        Formatter.Construction built = build(EVERY_FORM);

        List<String> unwritten = new ArrayList<>();
        for (SyntaxNode n : allOf(root)) {
            if (n.kind() == SyntaxKind.SOURCE_FILE) {
                continue;
            }
            if (built.places().placesOf(new Written.Construct(n)).isEmpty()
                    && built.places().spanOf(n) == null) {
                unwritten.add(n.kind() + " at " + n.start());
            }
        }

        assertEquals(List.of(), unwritten,
                "the construction records a place or a span for every construct it writes");
    }

    /**
     * A run the canonical form flattens says where it opens and where it ends.
     *
     * <p>{@code 1 |> b} of {@code 1 |> b |> c} is not a construct the canonical form has: what it
     * has is a head and two stages, and the nesting the parser read is spread over them. So the
     * construct opens at the head place and ends at the stage its own right operand is written at,
     * and both are recorded where they are written. Read off the source tree afterwards, the first
     * and last children of that operand are {@code 1} and {@code b}, and the place of the second is
     * only the right answer by accident of this shape.
     */
    @Test
    void andARunTheCanonicalFormFlattensSaysWhereItOpensAndWhereItEnds() {
        Formatter.Construction built = build("""
                module m
                let piped = 1 |> b |> c
                """);
        List<SyntaxNode> pipes = allOf(SyntaxKind.PIPE_EXPR);
        SyntaxNode whole = pipes.get(0);
        SyntaxNode inner = pipes.get(1);

        Correspondence.Span span = built.places().spanOf(inner);
        Correspondence.Span outer = built.places().spanOf(whole);

        assertSame(outer.from(), span.from(), "both runs open at the head the file writes first");
        assertNotSame(outer.to(), span.to(), "and they end at different stages");
        assertEquals(List.of(new Written.Construct(exprsOf(inner).get(1))),
                built.places().sourcesOf(span.to()),
                "the inner run ends at the stage its own right operand is written at");
    }

    /** One of everything, so that the answer above is quantified over the forms rather than over
     *  the ones someone thought to write down. */
    private static final String EVERY_FORM = """
            module m exposing ( A, S, run )
            import other.mod ( Thing )

            data A =
                { id: Int
                , pair: (Int, String)
                }

            data Small = Int
                invariant value > 0

            data One

            data Two

            data S = One | Two

            behavior run : (a: A, n: Int) -> A | Small
                constructs A, other.mod.Thing
                depends on helper

            let helper (n: Int) = n

            let run (a, n, helper) = {
                let doubled = helper(n) |> helper |> helper
                let list = [x | x > 0]
                guard doubled > 0 else Small(1)
                match value(a) with
                    | One -> A { ...a, id = doubled + 1 * 2 }
                    | Two -> A { ...a, id = 0 }
            }

            let value (a: A) = if a.id > 0 then One else Two

            let curried = (x) -> (y) -> x

            example helper
                | "it doubles" : (2) with n = 2 -> 2

            fake helper
                | (2) -> 4
            """;

    // --- reading the tree ---
    //
    // One parse per fixture, and every lookup goes through that one root. A place says which source
    // element it was written from by holding the element itself, and the tree hands back one node
    // per position — so a second parse of the same text is a different tree, and nothing written
    // from the first is found in it.

    private SyntaxNode root;

    private Correspondence placesOf(String src) {
        return build(src).places();
    }

    private Formatter.Construction build(String src) {
        root = CstParser.parse(src).root();
        return Formatter.build(root);
    }

    private static SyntaxNode childOf(SyntaxNode n, SyntaxKind kind) {
        return n.child(kind).orElseThrow();
    }

    private static List<SyntaxNode> allOf(SyntaxNode from) {
        List<SyntaxNode> out = new ArrayList<>();
        out.add(from);
        for (SyntaxNode c : from.childNodes()) {
            out.addAll(allOf(c));
        }
        return out;
    }

    /** The children of {@code n}, which for a run's node are its two operands. */
    private static List<SyntaxNode> exprsOf(SyntaxNode n) {
        return n.childNodes();
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
