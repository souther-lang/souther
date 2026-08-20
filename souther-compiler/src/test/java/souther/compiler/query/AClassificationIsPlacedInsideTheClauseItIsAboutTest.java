package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorContract;
import souther.compiler.check.ClauseDischarge;
import souther.compiler.check.ContractDischarge;
import souther.compiler.check.ContractDischarge.RuleDischarge;
import souther.compiler.diag.Region;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the compiler says about a clause is said where that clause is written.
 *
 * <p>Both kinds of clause are classified by asking the same check about an expression, and an
 * expression reaches it expanded — a helper the clause names is substituted first, because the
 * analysis has rules about what a clause states and none about a call. An expansion carries the
 * positions of the body it copies in, so a classification worked out from one and then placed by
 * what it was worked out from lands inside the helper, in a definition the author was not looking at.
 * The editor keeps the answers whose position falls inside the clause the cursor is in, so what an
 * author sees is a clause the compiler has nothing to say about.
 *
 * <p>This holds the property rather than the arrangement that keeps it. Where the split and the
 * placing happen relative to the expansion is a thing a reader can get wrong once per kind of clause
 * — it was written twice and was wrong in one of them — and every future reader of a clause has the
 * same order to get right.
 */
class AClassificationIsPlacedInsideTheClauseItIsAboutTest {

    /**
     * Clauses of both kinds that name helpers, with a helper written before the declaration that
     * names it and one written after, and a helper body that is itself a conjunction — which is what
     * splits one rule the author wrote into two answers where the splitting is done after expanding.
     */
    private static final String SOURCE = """
            module m.a exposing ( Amount, Id, Found, findIt )

            let positive (n: Int): Bool = n > 0
            let ranked (rank: Int, floor: Int): Bool = rank > 0 && rank > floor

            data Amount = Int
                invariant positive(value)
                invariant isSmall = value < 1000 && positive(value)

            data Id    = { n: Int }
            data Found = { rank: Int }

            behavior findIt : (id: Id) -> Found
                constructs Found
                ensures ranked(value.rank, id.n)
                ensures alsoPositive = positive(value.rank) && value.rank > id.n

            let findIt (id) = Found { rank = 1 }

            let atLeast (n: Int, floor: Int): Bool = n >= floor
            """;

    private static Compilation compiled() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", SOURCE);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
    }

    /** A position is inside a region, said so that neither being absent passes for agreement —
     *  {@link Region#encloses} is vacuously true where either side is nowhere. */
    private static void enclosedBy(Region clause, ClauseDischarge answer, String what) {
        assertNotNull(clause, what + ": the clause knows where it is written");
        assertNotNull(answer.owed().clause(), what + ": the answer says where it is about");
        assertTrue(Region.encloses(clause, Region.point(answer.owed().clause())),
                what + ": answered at " + answer.owed().clause() + ", which is not inside " + clause);
    }

    @Test
    void everyRuleIsPlacedInsideTheEnsuresItIsWrittenUnder() {
        Compilation c = compiled();
        Map<String, BehaviorContract> contracts = c.db().ask(new Bodies.Contracts("m.a")).value();
        Map<String, ContractDischarge> classified =
                c.db().ask(new Bodies.ContractCapabilities("m.a")).value();
        assertNotNull(contracts);
        assertNotNull(classified);

        ContractDischarge discharge = classified.get("findIt");
        assertNotNull(discharge, "the behavior states something, so it is classified");
        assertEquals(3, discharge.rules().size(),
                "one answer per conjunct the author wrote: the helper's own `&&` is not theirs");
        for (RuleDischarge rule : discharge.rules()) {
            BehaviorContract.Clause clause =
                    contracts.get("findIt").clauses().get(rule.rule().clause());
            enclosedBy(clause.region(), rule.capability(), "rule of clause " + rule.rule().clause());
        }
    }

    @Test
    void everyClauseIsPlacedInsideTheInvariantItIsWrittenUnder() {
        Compilation c = compiled();
        Map<TypeSymbol, List<Hir.InvariantClause>> declared =
                c.db().ask(new Shapes.InvariantsForDischarge("m.a")).value();
        Map<TypeSymbol, List<ClauseDischarge>> classified =
                c.db().ask(new Shapes.InvariantCapabilities("m.a")).value();
        assertNotNull(declared);
        assertNotNull(classified);
        assertEquals(1, classified.size(), "one declaration writes invariants here");

        classified.forEach((named, answers) -> {
            assertEquals(3, answers.size(),
                    "one answer per conjunct written: `positive(value)`, and the two of `isSmall`");
            for (ClauseDischarge answer : answers) {
                // Which of the declaration's clauses each answer is about is not carried, so what is
                // held is that it is inside one of them — a position inside the helper is inside none.
                boolean inside = false;
                for (Hir.InvariantClause clause : declared.get(named)) {
                    assertNotNull(clause.region(), "the clause knows where it is written");
                    inside = inside || Region.encloses(clause.region(), Region.point(answer.owed().clause()));
                }
                assertTrue(inside, "answered at " + answer.owed().clause()
                        + ", which is inside no clause of " + named);
            }
        });
    }
}
