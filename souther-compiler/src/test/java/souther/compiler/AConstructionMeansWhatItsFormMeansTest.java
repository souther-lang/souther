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
 * What a row wrote is more than the names it wrote.
 *
 * <p>An expected value is built as the value the row wrote rather than read through the position it
 * stands at, and the name a value wears is one part of what a row wrote. The form it was written in
 * is another: {@code Set.fromList([1])} states a set, a newtype states that its own declaration
 * admits what it wraps, a map states that its keys are distinct, and a record states a value for
 * every field it has. None of those is the position's to supply either.
 *
 * <p>Which of the two a failure is stays the same question. A row that could not build the value it
 * wrote states no expectation and is <em>E1903</em>; a row that built one the behavior did not answer
 * with is the disagreement it is, <em>E1905</em>.
 */
class AConstructionMeansWhatItsFormMeansTest {

    private static final String BASE = """
            module demo

            data AmountN = Int
            data Positive = Int
                invariant value > 0
            data NonEmpty = List<Int>
                invariant List.length(value) >= 1
            data Amounts = List<AmountN>
            data Receipt = { total: AmountN }
            data Held = { total: AmountN, note: String? }
            data Coded = { by: Map<String, Int> }

            behavior listOf : (n: Int) -> List<Int>
            let listOf (n) = [n]

            behavior emptyListOf : (n: Int) -> List<Int>
            let emptyListOf (n) = []

            behavior setOf : (n: Int) -> Set<Int>
            let setOf (n) = Set.fromList([n])

            behavior mapOf : (n: Int) -> Map<String, Int>
            let mapOf (n) = Map.fromList([("a", n)])

            behavior nonEmptyOf : (n: Int) -> NonEmpty
                constructs NonEmpty
            let nonEmptyOf (n) = NonEmpty([n])

            behavior heldAmounts : (n: Int) -> Amounts
                constructs Amounts, AmountN
            let heldAmounts (n) = Amounts([AmountN(n)])

            behavior positiveOf : (n: Int) -> Positive
                constructs Positive
            let positiveOf (n) = Positive(n)

            behavior receiptOf : (n: Int) -> Receipt
                constructs Receipt, AmountN
            let receiptOf (n) = Receipt { total = AmountN(n) }

            behavior heldOf : (n: Int) -> Held
                constructs Held, AmountN
            let heldOf (n) = Held { total = AmountN(n), note = None }

            behavior codedOf : (n: Int) -> Coded
                constructs Coded
            let codedOf (n) = Coded { by = Map.fromList([("a", n)]) }

            let neg (n: Int): Int = 0 - n
            let ints (n: Int): List<Int> = [n]
            let intSet (n: Int): Set<Int> = Set.fromList([n])
            """;

    private static void holds(String rows) {
        Compiler.compile(BASE + rows);
    }

    private static Diagnostic only(String rows) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(BASE + rows),
                "the row does not state what the behavior answered with");
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        return e.diagnostics().get(0);
    }

    /** The row built no value at all. */
    private static String couldNotBuild(String rows) {
        Diagnostic d = only(rows);
        assertEquals("E1903", d.code(), d.said().toString());
        return assertInstanceOf(ExampleMessage.TheExpectedValueCouldNotBeBuilt.class, d.said()).why();
    }

    /** The row built a value, and it is not the one that came out. */
    private static void doesNotHold(String rows) {
        Diagnostic d = only(rows);
        assertEquals("E1905", d.code(), d.said().toString());
        assertInstanceOf(ExampleMessage.TheRowDoesNotHold.class, d.said());
    }

    // --- which collection a row wrote -----------------------------------------------------------

    @Test
    void aRowThatWritesASetHasNotWrittenAList() {
        holds("""
                example listOf
                    | (1) -> [1]
                """);
        holds("""
                example setOf
                    | (1) -> Set.fromList([1])
                """);
        // `Set.fromList` states a set wherever it is written. A list of the same elements is not one,
        // and the position it stands at does not get to say it is.
        doesNotHold("""
                example listOf
                    | (1) -> Set.fromList([1])
                """);
    }

    @Test
    void anEmptyCollectionStatesWhichOneItIsWhenTheRowNamesIt() {
        // `[]` says nothing, so the position answers; `Set.empty` says it, so it does.
        holds("""
                example emptyListOf
                    | (1) -> []
                """);
        doesNotHold("""
                example emptyListOf
                    | (1) -> Set.empty
                """);
    }

    @Test
    void aHelpersAnswerStatesWhichCollectionItIs() {
        holds("""
                example listOf
                    | (1) -> ints(1)
                """);
        holds("""
                example setOf
                    | (1) -> intSet(1)
                """);
        doesNotHold("""
                example listOf
                    | (1) -> intSet(1)
                """);
        doesNotHold("""
                example setOf
                    | (1) -> ints(1)
                """);
    }

    @Test
    void bothSidesAreShownSayingWhichCollectionTheyAre() {
        // A mismatch nothing can be read in is the defect this walk was written for. Two sequences
        // written alike, differing only in which collection they are, were shown as one another.
        Diagnostic d = only("""
                example listOf
                    | (1) -> intSet(1)
                """);
        assertEquals("Set.fromList([ 1 ])", d.diff().expectedType());
        assertEquals("[ 1 ]", d.diff().actualType());
        assertTrue(d.notes().stream().anyMatch(note ->
                        note.said() instanceof ExampleMessage.TheTwoAreOfDifferentTypes(
                                String _, String stated, String answered)
                                && stated.equals("a set") && answered.equals("a list")),
                "the row is told which two collections it is between: " + d.notes());
    }

    @Test
    void aMapIsNotASequence() {
        holds("""
                example mapOf
                    | (1) -> Map.fromList([("a", 1)])
                """);
        doesNotHold("""
                example listOf
                    | (1) -> Map.empty
                """);
    }

    // --- what a construction admits of its own ---------------------------------------------------

    @Test
    void aNewtypeReadsItsOwnDeclarationOfWhateverItWraps() {
        holds("""
                example positiveOf
                    | (1) -> Positive(1)
                """);
        // Its invariant is its own, so it is read whether the value it wraps was spelled out or
        // answered by a helper. Reading one and not the other made the same row two outcomes.
        assertEquals("must be positive", couldNotBuild("""
                example positiveOf
                    | (1) -> Positive(-1)
                """));
        assertEquals("must be positive", couldNotBuild("""
                example positiveOf
                    | (1) -> Positive(neg(1))
                """));
    }

    @Test
    void aNewtypeInvariantIsReadWhateverItWraps() {
        // Its own decoder carries the whole of its invariant, so what a newtype wraps is not what
        // decides whether the invariant is read. Reading it only over a scalar left every collection
        // a newtype names outside a rule it declares.
        holds("""
                example nonEmptyOf
                    | (1) -> NonEmpty([1])
                """);
        assertEquals("must not be empty", couldNotBuild("""
                example nonEmptyOf
                    | (1) -> NonEmpty([])
                """));
    }

    @Test
    void whatANewtypeTakesIsAskedBeforeAnythingIsRun() {
        // The order matters. `Amounts` holds `AmountN`s, so a row writing numbers has written no
        // `Amounts` — and asking that of the written value is what keeps its decoder from being handed
        // the list and reading each number as the `AmountN` the position wanted.
        String why = couldNotBuild("""
                example heldAmounts
                    | (1) -> Amounts([1])
                """);
        assertTrue(why.contains("List<AmountN>"), why);
    }

    @Test
    void aMapsKeysAreDistinct() {
        holds("""
                example codedOf
                    | (1) -> Coded { by = Map.fromList([("a", 1)]) }
                """);
        // Two entries under one key state no map, which is not a disagreement with the behavior.
        couldNotBuild("""
                example codedOf
                    | (1) -> Coded { by = Map.fromList([("a", 1), ("a", 2)]) }
                """);
    }

    @Test
    void aRecordStatesAValueForEveryFieldItHas() {
        // Leaving a field out is how an optional is written empty, and it is only that.
        holds("""
                example heldOf
                    | (1) -> Held { total = AmountN(1) }
                """);
        couldNotBuild("""
                example receiptOf
                    | (1) -> Receipt { }
                """);
    }
}
