package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An {@code example} row may name a value instead of writing the whole input again. Four rows over a
 * four-band matrix were four copies of one record differing in a field, because a fixture had no way
 * to refer to one.
 *
 * <p>What a fixture may name is a property of the value graph, not of one definition's text: a value
 * is fixture-evaluable when it is a literal, a construction, a spread, or a reference to another
 * fixture-evaluable value. So a chain of values holds even though each link names the next.
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

    @Test
    void aValueThatIsNotAFixtureCannotBeNamedByARow() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data Lead = { name: String, score: Int }
                data Accepted
                data Rejected

                let raise (n) = n + 1
                let acme = Lead { name = "Acme", score = raise(71) }

                behavior qualify : (l: Lead) -> Accepted | Rejected
                    constructs Accepted, Rejected

                let qualify (l) = if l.score >= 70 then Accepted else Rejected

                example qualify
                    | "a computed field is not a fixture" : (acme) -> Accepted
                """));

        assertTrue(e.getMessage().contains("fixture"), e.getMessage());
    }
}
