package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.CheckSurface;
import souther.compiler.check.DerivedSymbols;
import souther.compiler.check.Normalized;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Deriving a representation and reading a declaration are two questions, and the first one's answer
 * does not choose the second one's.
 *
 * <p>Two things happen to a declaration below the settling. Its clauses are normalized — the newtype
 * constructions in them written as the constructions they denote — which is declaration-local and
 * asks nothing of the shapes its fields name. And a product has a decoder and an encoder read off
 * its declared shape, which a product one of whose fields names no type has none to read.
 *
 * <p>Read through one table, the second decided the first: a declaration whose representation came
 * out was handed over normalized and one whose did not was handed over as it was written, and
 * nothing a reader held said which it had. That is the shape #1239 was reported as, one rung down —
 * so what is held here is that the reading does not move when the derivation fails.
 */
class WhetherARepresentationCameOutDoesNotChooseHowADeclarationIsReadTest {

    /**
     * Two declarations of one module: one a representation can be derived for, one not.
     *
     * <p>Both write a construction in a clause, so both have something for the normalization to do
     * and a reader can tell the two forms apart. {@code Bad}'s field names no type, which is what
     * leaves it without a representation.
     */
    private static final String SOURCE = """
            module m exposing ( Wrapped, Good )

            data Wrapped = Int

            data Good = { n: Int }
                invariant ok = Wrapped(n) == Wrapped(0)

            data Bad = { v: Nowhere }
                invariant fine = Wrapped(0) == Wrapped(0)
            """;

    /** The same module with nothing in it a representation cannot be derived for. */
    private static final String WHOLE = """
            module m exposing ( Wrapped, Good )

            data Wrapped = Int

            data Good = { n: Int }
                invariant ok = Wrapped(n) == Wrapped(0)

            data Bad = { v: Int }
                invariant fine = Wrapped(0) == Wrapped(0)
            """;

    private static Db db(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("m.sou", source);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY).db();
    }

    private static final TypeKey GOOD = new TypeKey("m", "Good");
    private static final TypeKey BAD = new TypeKey("m", "Bad");

    /** The two are told apart: one has a representation and the other has none. */
    @Test
    void oneOfThemHasARepresentationAndTheOtherHasNone() {
        Db db = db(SOURCE);

        assertTrue(db.ask(new Shapes.DerivedDef(GOOD)).present(), "`Good` has one derived");
        assertFalse(db.ask(new Shapes.DerivedDef(BAD)).present(),
                "`Bad` holds a field naming nothing, so nothing derived one for it");
    }

    /** And both are read as the normalized producer wrote them. */
    @Test
    void bothAreReadAsTheNormalizedProducerWroteThem() {
        Db db = db(SOURCE);
        DerivedSymbols symbols = Scopes.derived(db, "m").value();

        assertSame(normalized(db, GOOD), symbols.declaredNode(GOOD),
                "the declaration a representation came out for");
        assertSame(normalized(db, BAD), symbols.declaredNode(BAD),
                "and the one it did not, which is the same producer's answer");
    }

    /**
     * The reading does not move when the derivation stops answering for a declaration.
     *
     * <p>The whole of it. One source derives for every declaration and the other does not, and
     * {@code Bad} is read the same way in both — so nothing about how a declaration is read is
     * decided by whether a representation could be derived for it.
     */
    @Test
    void theReadingIsTheSameWhereTheDerivationAnsweredAndWhereItDidNot() {
        Hir.Def whereItFailed = Scopes.derived(db(SOURCE), "m").value().declaredNode(BAD);
        Hir.Def whereItCameOut = Scopes.derived(db(WHOLE), "m").value().declaredNode(BAD);

        assertNotNull(whereItFailed, "`Bad` is declared either way");
        assertEquals(0, applications(clauseOf(whereItFailed)),
                "its clause holds constructions where nothing derived a representation for it");
        assertEquals(0, applications(clauseOf(whereItCameOut)),
                "and where one was derived, which is the same reading");
    }

    /** And the surface a check reads holds that same declaration, from that same producer. */
    @Test
    void theSurfaceHoldsWhatTheNormalizedProducerAnswered() {
        Db db = db(SOURCE);
        CheckSurface surface = db.ask(new Shapes.CheckSurface("m")).value();

        assertNotNull(surface, "a module one declaration of which has no representation is read");
        for (Hir.Def each : surface.module().defs()) {
            assertSame(normalized(db, each.declaredKey()), each,
                    "`" + each.name() + "` on the surface is the declaration the producer answered"
                            + " with, and not one worked out a second time");
        }
    }

    private static Hir.Def normalized(Db db, TypeKey named) {
        Normalized.Def def = db.ask(new Shapes.NormalizedDef(named)).value();
        assertNotNull(def, "`" + named.name() + "` is normalized");
        return def.node();
    }

    private static Hir.Expr clauseOf(Hir.Def def) {
        return ((Hir.Data) def).invariants().get(0).expr();
    }

    private static int applications(Hir.Expr e) {
        if (e == null) {
            return 0;
        }
        int[] found = {e instanceof Hir.Apply ? 1 : 0};
        Hir.forEachChild(e, c -> found[0] += applications(c));
        return found[0];
    }
}
