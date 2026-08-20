package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.ExampleMessage;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row is held to what it wrote, and to nothing the position writes for it.
 *
 * <p>An expected value used to be read through the decoder of the position it stood at, and a derived
 * decoder puts its own name on the base it reads. So a field written as a number came back wearing
 * the name its field declared, and the row was compared against a value it had not stated: it held,
 * and what made it hold was the reading rather than the behavior.
 *
 * <p>What replaces it is not admission. A row may state what the behavior does not answer with —
 * reporting that disagreement is what a row is for — so what a row wrote is built as a value of its
 * own and the two are compared. Where they differ by their type rather than their contents, that is
 * what the row is told, at the position they part.
 *
 * <p>Held at every depth, because the decode was: a field, an element, an element of an element, a
 * map's value and a map's key are each a position of their own.
 */
class AnExpectedValueIsNotDecodedIntoItsPositionTest {

    private static final String BASE = """
            module demo

            data AmountN = Int
            data OtherAmountN = Int
            data Rejected = { why: String }
            data Code = String

            data Receipt = { total: AmountN }
            data Bag = { items: List<AmountN> }
            data Book = { by: Map<String, AmountN> }
            data Keyed = { by: Map<Code, String> }

            behavior receiptOf : (n: Int) -> Receipt
                constructs Receipt, AmountN
            let receiptOf (n) = Receipt { total = AmountN(n) }

            behavior bagOf : (n: Int) -> Bag
                constructs Bag, AmountN
            let bagOf (n) = Bag { items = [AmountN(n)] }

            behavior bookOf : (n: Int) -> Book
                constructs Book, AmountN
            let bookOf (n) = Book { by = Map.fromList([("a", AmountN(n))]) }

            behavior keyedOf : (n: Int) -> Keyed
                constructs Keyed, Code
            let keyedOf (n) = Keyed { by = Map.fromList([(Code("k"), "a")]) }

            behavior manyOf : (n: Int) -> List<AmountN>
                constructs AmountN
            let manyOf (n) = [AmountN(n)]

            behavior nestedOf : (n: Int) -> List<List<AmountN>>
                constructs AmountN
            let nestedOf (n) = [[AmountN(n)]]

            behavior bareOf : (n: Int) -> Int | Rejected
                constructs Rejected
            let bareOf (n) = if n > 0 then n else Rejected { why = "no" }

            behavior namedOf : (n: Int) -> AmountN | Rejected
                constructs AmountN, Rejected
            let namedOf (n) = if n > 0 then AmountN(n) else Rejected { why = "no" }
            """;

    private static void holds(String rows) {
        Compiler.compile(BASE + rows);
    }

    private static Diagnostic only(String rows) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(BASE + rows),
                "the row states a value the behavior did not answer with");
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        return e.diagnostics().get(0);
    }

    /**
     * The construction cannot be stated: a field of it takes another type. Where the rule stops in
     * the static direction — a construction of the output's own type is held to its own field
     * declarations, as it is in a body, so a row stating another type inside one has not written a
     * value to compare. The comparison (E1905) is for values that build.
     */
    private static void refusedToBuild(String rows, String... names) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(BASE + rows),
                "the construction misstates its own field");
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        assertEquals("E1317", e.diagnostics().get(0).code(), e.getMessage());
        for (String name : names) {
            assertTrue(e.getMessage().contains(name), "`" + name + "` is said: " + e.getMessage());
        }
    }

    /** The row does not hold, and it is told where the two part and which two types they are. */
    private static void differsBy(String rows, String at, String expected, String actual) {
        Diagnostic d = only(rows);
        assertEquals("E1905", d.code(), d.said().toString());
        assertInstanceOf(ExampleMessage.TheRowDoesNotHold.class, d.said());
        assertTrue(d.notes().stream().anyMatch(note ->
                        note.said() instanceof ExampleMessage.TheTwoAreOfDifferentTypes(
                                String where, String stated, String answered)
                                && where.equals(at) && stated.equals(expected)
                                && answered.equals(actual)),
                "expected " + expected + " and " + actual + " at " + at + ": " + d.notes());
    }

    @Test
    void aFieldWrittenAsTheBaseIsNotAValueOfTheNameTheFieldDeclares() {
        holds("""
                example receiptOf
                    | (1) -> Receipt { total = AmountN(1) }
                """);
        refusedToBuild("""
                example receiptOf
                    | (1) -> Receipt { total = 1 }
                """, "AmountN", "Int");
    }

    @Test
    void twoNamesOverOneBaseAreTwoTypesAtAField() {
        // The reading that lost the name lost it for every name over that base, so a row could state
        // one newtype and be compared against another.
        refusedToBuild("""
                example receiptOf
                    | (1) -> Receipt { total = OtherAmountN(1) }
                """, "AmountN", "OtherAmountN");
    }

    @Test
    void anElementIsAPositionOfItsOwn() {
        holds("""
                example bagOf
                    | (1) -> Bag { items = [AmountN(1)] }
                """);
        refusedToBuild("""
                example bagOf
                    | (1) -> Bag { items = [1] }
                """, "List<AmountN>", "List<Int>");
    }

    @Test
    void soIsAnElementOfAnElement() {
        holds("""
                example nestedOf
                    | (1) -> [[AmountN(1)]]
                """);
        differsBy("""
                example nestedOf
                    | (1) -> [[1]]
                """, "$[0][0]", "Int", "AmountN");
    }

    @Test
    void aCollectionAtTheTopIsReadTheSameWay() {
        // The one place the old reading did not decode was a top-level value that was not a
        // collection. A collection there went through the decode with everything else.
        holds("""
                example manyOf
                    | (1) -> [AmountN(1)]
                """);
        differsBy("""
                example manyOf
                    | (1) -> [1]
                """, "$[0]", "Int", "AmountN");
    }

    @Test
    void aMapsValueIsAPositionOfItsOwn() {
        holds("""
                example bookOf
                    | (1) -> Book { by = Map.fromList([("a", AmountN(1))]) }
                """);
        refusedToBuild("""
                example bookOf
                    | (1) -> Book { by = Map.fromList([("a", 1)]) }
                """, "Map<String, AmountN>", "Map<String, Int>");
    }

    @Test
    void soIsAMapsKey() {
        holds("""
                example keyedOf
                    | (1) -> Keyed { by = Map.fromList([(Code("k"), "a")]) }
                """);
        // A key the row writes under no name is not a key of the map the field declares, and the
        // construction is refused as it is in a body.
        refusedToBuild("""
                example keyedOf
                    | (1) -> Keyed { by = Map.fromList([("k", "a")]) }
                """, "Map<Code, String>", "Map<String, String>");
    }

    @Test
    void anAnonymousUnionTakesTheCaseTheRowWroteWhetherOrNotItWearsAName() {
        // Whether a nameless value belongs at such a position is the comparison's question: the
        // position holds an `Int` here and an `AmountN` there, and neither reads the other's row.
        holds("""
                example bareOf
                    | (1) -> 1
                """);
        holds("""
                example namedOf
                    | (1) -> AmountN(1)
                """);
        differsBy("""
                example namedOf
                    | (1) -> 1
                """, "$", "Int", "AmountN");
        // Where the two questions meet. A name the output does not list at all is read before
        // anything is compared, and is reported as the case it is not rather than as a type the two
        // differ by. Only a value that got past that is compared, which is every position under it.
        Diagnostic d = only("""
                example bareOf
                    | (1) -> AmountN(1)
                """);
        assertEquals("E1904", d.code(), d.said().toString());
        assertInstanceOf(ExampleMessage.NotOneOfTheResultCases.class, d.said());
    }

    @Test
    void aRowExpectingACaseTheBehaviorDoesNotAnswerWithStillReportsThat() {
        // The rule an expected value is not admitted for. Stating what the behavior did not answer
        // with is what a row is for, so it is a disagreement and never a fixture that could not be
        // built.
        Diagnostic d = only("""
                example namedOf
                    | (1) -> Rejected { why = "no" }
                """);
        assertEquals("E1905", d.code(), d.said().toString());
        assertInstanceOf(ExampleMessage.TheRowDoesNotHold.class, d.said());
    }

    @Test
    void aValueThatCannotBeBuiltIsStillAFixtureError() {
        // Where the rule stops in the other direction. `AmountN("x")` states no value at all — its
        // own base takes a number — which is not a disagreement with the behavior but a fixture that
        // could not be built.
        refusedToBuild("""
                example receiptOf
                    | (1) -> Receipt { total = AmountN("x") }
                """, "Int", "String");
    }
}
