package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Names;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertAll;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A walk over the spreads comes back, whatever graph it is handed, and says what it left out.
 *
 * <p>Two contracts and this is the second one. That a data does not spread itself is the language's,
 * said once and before any of these run
 * ({@link ADataThatSpreadsItsWayBackToItselfIsRefusedTest}); that a walk over what a declaration
 * spreads terminates is each walk's own, and holds of a graph nobody validated. The reason for
 * keeping them apart is what the first contract cannot promise: which readers run before which is a
 * property of the query graph, and an edge added there is not something a walk written today can be
 * asked to have known.
 *
 * <p><b>Coming back is half of it.</b> A walk that cuts an edge has left rules out, and a carrier
 * that says whether every rule was reached has to say so — handed back as complete, some of the
 * clauses of a ring would be read as all of them, and which some depends on which of the ring's
 * declarations was asked for first. Neither walk says anything about the ring itself: what a reader
 * of one is owed is the refusal, and that is somewhere else.
 *
 * <p><b>Walks of three lineages.</b> What the declarations publish, what a world's expansion states,
 * and the trees a world holds. The second was the next to run out of stack when the first was made
 * finite, which is why none of them is taken as standing for the others. Each is paired with a chain
 * it does reach through, because a walk that answered without crossing a spread would come back on a
 * ring for the wrong reason.
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
    void whatTheDeclarationsPublishIsWalkedThroughASpreadAndComesBackShortOnARing() {
        PublishedRules chain = rulesPublishedFor(A_CHAIN, "Left");
        PublishedRules ring = rulesPublishedFor(A_RING, "Pair");

        assertAll(
                () -> assertEquals(1, chain.reached().size(),
                        "the rule written on what `Left` spreads is reached through the spread"),
                () -> assertTrue(chain.everyRuleReached(),
                        "and nothing was left out on the way to it"),
                () -> assertFalse(ring.everyRuleReached(),
                        "a ring is walked round once, and what that leaves is rules not reached"));
    }

    @Test
    void whatAWorldsExpansionStatesIsWalkedThroughASpreadAndComesBackShortOnARing() {
        ExpandedRules chain = expandedRulesFor(A_CHAIN, "Left");
        ExpandedRules ring = expandedRulesFor(A_RING, "Pair");

        assertAll(
                () -> assertEquals(1, chain.whole().orElseThrow().size(),
                        "the rule written on what `Left` spreads is reached through the spread"),
                () -> assertEquals(Optional.empty(), ring.whole(),
                        "nothing may take what a ring left as the rules that govern the value"));
    }

    /**
     * And the trees, which carry the clauses and nothing beside them.
     *
     * <p>Only that it comes back, because there is nothing here to say it is short with: what this
     * hands over is the clauses it reached, and a reader wanting to know whether that was all of
     * them asks the reading above, which says.
     */
    @Test
    void theClausesAWorldHoldsAreWalkedThroughASpreadAndComeBackOnARing() {
        assertEquals(1, settledClausesFor(A_CHAIN, "Left").size(),
                "the clause written on what `Left` spreads is reached through the spread");

        assertNotNull(settledClausesFor(A_RING, "Pair"),
                "a ring is walked round once rather than for ever");
    }

    /** What the declarations publish about {@code declared}, walked from a reading of the module. */
    private static PublishedRules rulesPublishedFor(String source, String declared) {
        return new Clauses(RuleReadings.of(compiled(source), "demo")).of(named(declared));
    }

    /** The same rules as the module's own expansion states them. */
    private static ExpandedRules expandedRulesFor(String source, String declared) {
        Db db = compiled(source);
        return TypeOps.expandedInvariants(named(declared), derivedWorldOf(db),
                RuleReadings.declaredBy(db, "demo"));
    }

    /** The clauses the derived world holds for {@code declared} and for what it spreads. */
    private static List<Hir.InvariantClause> settledClausesFor(String source, String declared) {
        return TypeOps.settledClausesGoverning(named(declared), derivedWorldOf(compiled(source)));
    }

    private static DerivedSymbols derivedWorldOf(Db db) {
        DerivedSymbols symbols = Names.derivedSymbols(db, "demo").value();
        assertNotNull(symbols, "a module has a derived world whatever it declares");
        return symbols;
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
