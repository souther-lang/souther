package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A row that did not hold is told the two in one order, and it is neither side's own.
 *
 * <p>Of the compile, which is where it matters that neither side has an order to lend. A row states
 * a value: what it wrote is run, and the map that comes back holds its pairs where the runtime's
 * table put them — the same kind of accident the answer's own order is. Asked of the two values in
 * hand, both look like somebody's sequence and neither is.
 *
 * <p>Written here rather than only where the order is decided, because a route that stopped carrying
 * one of the two would still write both out and would look right at every place that decides
 * anything.
 */
class ARowIsToldItsAnswerInOneOrderTest {

    private static final String MODEL = """
            module m

            data Book = { by: Map<String, Int> }

            behavior bookOf : (n: Int) -> Book
                constructs Book

            let bookOf (n) = Book { by = Map.fromList([ ("zeta", 1), ("alpha", 2), ("mu", 3) ]) }
            """;

    /**
     * Neither the order the row wrote nor the one either value came out holding.
     *
     * <p>The names are chosen so the three orders are three: the row writes {@code mu}, {@code zeta},
     * {@code alpha}, the tables walk them another way, and what is shown is the one this compiler
     * settles on.
     */
    @Test
    void theTwoAreWrittenInOneOrderThatIsNeitherSidesOwn() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(MODEL + """

                example bookOf
                    | (0) -> Book { by = [ ("mu", 9), ("zeta", 1), ("alpha", 2) ] }
                """));
        Diagnostic said = e.diagnostics().getFirst();

        assertEquals("E1905", said.code(), e.getMessage());
        assertEquals("Book { by = Map.fromList([ (\"alpha\", 2), (\"mu\", 9), (\"zeta\", 1) ]) }",
                said.diff().expectedType(), e.getMessage());
        assertEquals("Book { by = [ (\"alpha\", 2), (\"mu\", 3), (\"zeta\", 1) ] }",
                said.diff().actualType(), e.getMessage());
    }
}
