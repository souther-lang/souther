package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A field taken off a value a row can already build. A spread copies every field of such a value and
 * was admitted; reading one of them back was not, so a fixture for a collection derived from another
 * value had to be written out again as a literal.
 *
 * <p>What a taken field supplies is its declaration's to say — which is the answer a value cannot
 * give where the field holds an empty collection, there being no element to name. Where the value is
 * one a helper answered with, the answer says it, as it does wherever a helper stands.
 */
class CompileFixtureProjectsAFieldTest {

    @Test
    void anExpectedValueReadsAFieldOffANamedValue() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Line = { done: Bool }
                data Ticket = { lines: List<Line> }

                let sample = Ticket { lines = [ Line { done = false } ] }

                behavior linesOf : (t: Ticket) -> List<Line>
                let linesOf (t) = t.lines

                example linesOf
                    | "an expected value reads a field" : (sample) -> sample.lines
                """));
    }

    /**
     * The case a value cannot answer. An empty list has no element to name, so what says the field
     * supplies a {@code List<AmountN>} is the declaration and nothing else.
     */
    @Test
    void aProjectedEmptyCollectionIsHeldToTheFieldsDeclaration() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data AmountN = Int
                data Basket = { amounts: List<AmountN> }

                let empty = Basket { amounts = [ ] }

                behavior countOf : (ns: List<Int>) -> Int
                let countOf (ns) = List.length(ns)

                example countOf
                    | "an empty list keeps the name its field declares" : (empty.amounts) -> 0
                """));
        // The reason and not the code: a fixture that cannot be read at all is E1903 too, so a row
        // asserting the code alone goes green while nothing has been held to any declaration.
        assertTrue(e.getMessage().contains("List<AmountN>") && e.getMessage().contains("List<Int>"),
                e.getMessage());
    }

    /** The control for the above: the same projection at the position its field declares. */
    @Test
    void aProjectedCollectionIsAdmittedAtItsOwnDeclaration() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data AmountN = Int
                data Basket = { amounts: List<AmountN> }

                let empty = Basket { amounts = [ ] }

                behavior countOf : (ns: List<AmountN>) -> Int
                let countOf (ns) = List.length(ns)

                example countOf
                    | "the same declaration is admitted" : (empty.amounts) -> 0
                """));
    }

    @Test
    void aProjectedValueIsAdmittedWhereAnOptionalHoldsIt() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data AmountN = Int
                data Basket = { total: AmountN }
                data Order = { total: AmountN? }

                let one = Basket { total = AmountN(100) }

                behavior hasTotal : (o: Order) -> Bool
                let hasTotal (o) = true

                example hasTotal
                    | "an optional field holds what a field declares" : (Order { total = one.total }) -> true
                """));
    }
}
