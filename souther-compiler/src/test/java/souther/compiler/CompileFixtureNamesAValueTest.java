package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An {@code example} row may name a value instead of writing the whole input again. Four rows over a
 * four-band matrix were four copies of one record differing in a field, because a fixture had no way
 * to refer to one.
 *
 * <p>What a fixture may name is a property of the value graph, not of one definition's text: a value
 * is fixture-evaluable when it is a literal, a construction, a spread, an empty collection, a helper
 * applied to those, or a reference to another fixture-evaluable value. So a chain of values holds even
 * though each link names the next.
 */
class CompileFixtureNamesAValueTest {

    @Test
    void aRowNamesAValueInsteadOfWritingTheInput() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Lead = { name: String, score: Int, budgetConfirmed: Bool }
                data Accepted
                data Rejected

                let acme = Lead { name = "Acme", score = 72, budgetConfirmed = true }

                behavior qualify : (l: Lead) -> Accepted | Rejected
                    constructs Accepted, Rejected

                let qualify (l) = if l.score >= 70 && l.budgetConfirmed then Accepted else Rejected

                example qualify
                    | "a confirmed budget qualifies" : (acme) -> Accepted
                """));
    }

    @Test
    void aRowSpreadsAValueAndOverridesAField() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Lead = { name: String, score: Int, budgetConfirmed: Bool }
                data Accepted
                data Rejected

                let acme = Lead { name = "Acme", score = 72, budgetConfirmed = true }

                behavior qualify : (l: Lead) -> Accepted | Rejected
                    constructs Accepted, Rejected

                let qualify (l) = if l.score >= 70 && l.budgetConfirmed then Accepted else Rejected

                example qualify
                    | "a confirmed budget qualifies" : (acme) -> Accepted
                    | "an unconfirmed budget does not" :
                        (Lead { ...acme, budgetConfirmed = false }) -> Rejected
                """));
    }

    @Test
    void aValueMayReachAFixtureThroughAnotherValue() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Score = Int
                data Lead = { name: String, score: Score }
                data Accepted
                data Rejected

                let passing = 72
                let acmeScore = Score(passing)
                let acme = Lead { name = "Acme", score = acmeScore }

                behavior qualify : (l: Lead) -> Accepted | Rejected
                    constructs Accepted, Rejected

                let qualify (l) = if l.score.value >= 70 then Accepted else Rejected

                example qualify
                    | "a chain of values is one fixture" : (acme) -> Accepted
                """));
    }

    /** A row writes a set as its elements, but a value is ordinary code, where a list literal is a
     * {@code List} whatever the position declares. {@code Set.fromList} is the form the row's own
     * notation stands for, so one record serves as both. */
    @Test
    void aValueReachesASetThroughTheFormTheRowNotationStandsFor() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data ContactId = String
                data Deal = { makers: Set<ContactId> }
                data Enough
                data TooFew

                let acme = Deal { makers = Set.fromList([ ContactId("c-1"), ContactId("c-2") ]) }

                behavior staffed : (d: Deal) -> Enough | TooFew
                    constructs Enough, TooFew

                let staffed (d) = if Set.size(d.makers) >= 2 then Enough else TooFew

                example staffed
                    | "two deciders is enough" : (acme) -> Enough
                """));
    }

    /** A value whose body is `Map.empty` — the form a fold seed takes, and the one a row could not
     * name while it could name the `Map.fromList([ ])` denoting the same map. */
    @Test
    void aValueReachesTheEmptyMapByName() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data AccountCode = String
                data Ledger = { balances: Map<AccountCode, Int> }
                data Balanced
                data Unbalanced

                let start: Map<AccountCode, Int> = Map.empty
                let opening = Ledger { balances = start }

                behavior settle : (l: Ledger) -> Balanced | Unbalanced
                    constructs Balanced, Unbalanced

                let settle (l) = if Map.size(l.balances) == 0 then Balanced else Unbalanced

                example settle
                    | "an opening ledger is balanced" : (opening) -> Balanced
                """));
    }

    /** The same across a module boundary, named and spread: a published value crosses closed, and the
     * empty collection inside it is still the library's name. */
    @Test
    void aPublishedValueCarriesTheEmptyMapAcross() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module up exposing ( AccountCode, Ledger, opening )

                data AccountCode = String
                data Ledger = { balances: Map<AccountCode, Int> }

                let opening = Ledger { balances = Map.empty }
                """, """
                module down
                import up ( Ledger, opening )

                data Balanced
                data Unbalanced

                behavior settle : (l: Ledger) -> Balanced | Unbalanced
                    constructs Balanced, Unbalanced

                let settle (l) = if Map.size(l.balances) == 0 then Balanced else Unbalanced

                example settle
                    | "an imported opening ledger is balanced" : (opening) -> Balanced
                    | "and so is a spread of it" : (Ledger { ...opening }) -> Balanced
                """)));
    }

    @Test
    void aValueWhoseBodyAppliesAHelperIsAFixture() {
        // The helper is run where the row is evaluated (ADR-0077), so the value states the rule
        // rather than restating its result: `raise(71)` is 72, and 72 qualifies.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Lead = { name: String, score: Int }
                data Accepted
                data Rejected

                let raise (n: Int) = n + 1
                let acme = Lead { name = "Acme", score = raise(71) }

                behavior qualify : (l: Lead) -> Accepted | Rejected
                    constructs Accepted, Rejected

                let qualify (l) = if l.score >= 70 then Accepted else Rejected

                example qualify
                    | "a raised score qualifies" : (acme) -> Accepted
                """));
    }

    private static final String VALUE_OVER_AN_INTRINSIC = """
            module demo

            data Lead = { name: String, score: Int }
            data Accepted
            data Rejected

            let acme = Lead { name = "Acme", score = String.length("Acme") }

            behavior qualify : (l: Lead) -> Accepted | Rejected
                constructs Accepted, Rejected

            let qualify (l) = if l.score >= 70 then Accepted else Rejected

            example qualify
            """;

    /** A value whose body applies an intrinsic is a fixture like one whose body applies any other
     * library function (#680). `String.length("Acme")` is 4, which does not qualify. */
    @Test
    void aValueWhoseBodyAppliesAnIntrinsicIsAFixture() {
        assertDoesNotThrow(() -> Compiler.compile(VALUE_OVER_AN_INTRINSIC
                + "    | \"a short name does not qualify\" : (acme) -> Rejected\n"));
    }

    /** And the score is the one the intrinsic answered, not one the row was let assume. */
    @Test
    void theValueTheIntrinsicAnsweredIsWhatTheRowIsHeldTo() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile(VALUE_OVER_AN_INTRINSIC
                        + "    | \"a short name does not qualify\" : (acme) -> Accepted\n"));
        assertEquals("E1905", e.diagnostic().code(), e.getMessage());
    }
}
