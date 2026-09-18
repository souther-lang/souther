package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Answer;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Names;
import souther.compiler.query.Shapes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A walk over the spreads comes back, whatever graph it is handed.
 *
 * <p>Two contracts and this is the second one. That a data does not spread itself is the language's,
 * said once and before any of these run
 * ({@link ADataThatSpreadsItsWayBackToItselfIsRefusedTest}); that a walk over what a declaration
 * spreads terminates is each walk's own, and holds of a graph nobody validated. The reason for
 * keeping them apart is what the first contract cannot promise: which readers run before which is a
 * property of the query graph, and an edge added there is not something a walk written today can be
 * asked to have known. A walk that would run out of stack on a ring is a compile that ends with
 * nothing said.
 *
 * <p>Neither walk says anything about the ring. What it comes back with on one is not an answer
 * anybody is meant to read — what a reader of a ring is owed is the refusal, and that is somewhere
 * else.
 *
 * <p><b>Two walks of different lineage.</b> One reads the declarations as their modules publish them
 * and the other reads the trees a world holds, which is the difference that made the second of them
 * the next to run out of stack when the first was made finite. Each is paired with a chain it does
 * reach through, because a walk that answered without crossing a spread would come back on a ring
 * for the wrong reason.
 */
class AWalkOverSpreadsComesBackOnAGraphTheLanguageRefusesTest {

    /** A spread that is crossed, with the rule to show for it on the far side. */
    private static final String A_CHAIN = """
            module demo exposing ( Held, Left )

            data Held = { n: Int }
                invariant n >= 1

            data Left = { ...Held, l: Bool }
            """;

    /** The graph the language refuses, with a rule on each so that a walk reaching one has
     *  something to come back with. */
    private static final String A_RING = """
            module demo exposing ( Pair, Other )

            data Pair  = { ...Other, qty: Int }
                invariant qty >= 1

            data Other = { ...Pair, note: String }
                invariant qty >= 0
            """;

    @Test
    void whatTheDeclarationsPublishIsWalkedThroughASpreadAndComesBackOnARing() {
        assertEquals(1, rulesPublishedFor(A_CHAIN, "Left").reached().size(),
                "the rule written on what `Left` spreads is reached through the spread");

        assertNotNull(rulesPublishedFor(A_RING, "Pair"),
                "a ring is walked round once rather than for ever");
    }

    @Test
    void theClausesAWorldHoldsAreWalkedThroughASpreadAndComeBackOnARing() {
        assertEquals(1, settledClausesFor(A_CHAIN, "Left").size(),
                "the clause written on what `Left` spreads is reached through the spread");

        assertNotNull(settledClausesFor(A_RING, "Pair"),
                "a ring is walked round once rather than for ever");
    }

    /** What the declarations publish about {@code declared}, walked from a reading of the module. */
    private static PublishedRules rulesPublishedFor(String source, String declared) {
        Db db = compiled(source);
        Answer<RuleReadingSource> reading = Shapes.ruleReading(db, "demo");
        assertNotNull(reading.value(), "a module has a reading of its rules whatever it declares");
        return new Clauses(reading.value()).of(named(declared));
    }

    /** The clauses the derived world holds for {@code declared} and for what it spreads. */
    private static List<Hir.InvariantClause> settledClausesFor(String source, String declared) {
        Db db = compiled(source);
        Answer<DerivedSymbols> symbols = Names.derivedSymbols(db, "demo");
        assertNotNull(symbols.value(), "a module has a derived world whatever it declares");
        return TypeOps.settledClausesGoverning(named(declared), symbols.value());
    }

    private static TypeSymbol.AtModule named(String declared) {
        return TypeSymbols.declared(new TypeKey("demo", declared));
    }

    private static Db compiled(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("m.sou", source);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        try {
            c.answerEverything();
        } catch (CompileException _) {
            // What a ring is refused with is another test's. This one asks the walks directly.
        }
        return c.db();
    }
}
