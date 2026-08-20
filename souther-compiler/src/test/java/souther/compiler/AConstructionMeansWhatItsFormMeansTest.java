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
            data Wrapped = Receipt
            data Span = { from: Int, to: Int }
                invariant from <= to
            data Priced = { at: Decimal }
                invariant at > 0m
            data Stamped = { from: DateTime, to: DateTime }
                invariant from <= to
            data Boxed = { held: AmountN? }
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

            behavior wrappedOf : (n: Int) -> Wrapped
                constructs Wrapped, Receipt, AmountN
            let wrappedOf (n) = Wrapped(Receipt { total = AmountN(n) })

            behavior boxedOf : (n: Int) -> Boxed
                constructs Boxed, AmountN
            let boxedOf (n) = Boxed { held = AmountN(n) }

            behavior widen : (s: Span) -> Span
                constructs Span
            let widen (s) = Span { from = s.from, to = s.to + 1 }

            behavior pricedOf : (n: Int) -> Priced
                constructs Priced
            let pricedOf (n) = Priced { at = 1m }

            behavior stampedOf : (n: Int) -> Stamped
                constructs Stamped
            let stampedOf (n) = Stamped { from = DateTime("2026-07-20T09:00"),
                to = DateTime("2026-07-21T09:00") }

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
    /**
     * The construction is refused where a body's is: a row's operand is compiled as this module's
     * code, so a field of another type, a missing field, a temporal where another temporal stands
     * are the language's own refusals at the position that misstates.
     */
    private static void refusedStatically(String rows, String code, String... names) {
        Diagnostic d = only(rows);
        assertEquals(code, d.code(), d.said().toString());
        for (String name : names) {
            assertTrue(d.toString().contains(name) || d.said().toString().contains(name),
                    "`" + name + "` is said: " + d.said());
        }
    }

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
        assertTrue(couldNotBuild("""
                example positiveOf
                    | (1) -> Positive(-1)
                """).contains("invariant violated on demo.Positive"));
        assertTrue(couldNotBuild("""
                example positiveOf
                    | (1) -> Positive(neg(1))
                """).contains("invariant violated on demo.Positive"));
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
        assertTrue(couldNotBuild("""
                example nonEmptyOf
                    | (1) -> NonEmpty([])
                """).contains("invariant violated on demo.NonEmpty"));
    }

    @Test
    void whatANewtypeTakesIsAskedBeforeAnythingIsRun() {
        // The order matters. `Amounts` holds `AmountN`s, so a row writing numbers has written no
        // `Amounts` — and asking that of the written value is what keeps its decoder from being handed
        // the list and reading each number as the `AmountN` the position wanted.
        refusedStatically("""
                example heldAmounts
                    | (1) -> Amounts([1])
                """, "E1317", "List<AmountN>", "List<Int>");
    }

    @Test
    void whatAConstructionTakesIsAValueAtEveryDepth() {
        // A construction takes a value, and a value has values under it. `Receipt { total = 1 }` is an
        // expectation of its own where nothing is built from it — the number at a named field is the
        // disagreement it reports — and is no argument at all where something is.
        holds("""
                example wrappedOf
                    | (1) -> Wrapped(Receipt { total = AmountN(1) })
                """);
        refusedStatically("""
                example wrappedOf
                    | (1) -> Wrapped(Receipt { total = 1 })
                """, "E1317", "AmountN", "Int");
        // And the same value on its own is refused the same way.
        refusedStatically("""
                example receiptOf
                    | (1) -> Receipt { total = 1 }
                """, "E1317", "AmountN", "Int");
    }

    @Test
    void anOptionalIsWhatItHoldsOrNothing() {
        // An optional was the one position this walk did not reach, so anything written under a `?`
        // was admitted unasked and its decoder read it as whatever the field declared.
        holds("""
                example boxedOf
                    | (1) -> Boxed { held = AmountN(1) }
                """);
        refusedStatically("""
                example boxedOf
                    | (1) -> Boxed { held = 1 }
                """, "E1317", "AmountN", "Int");
        doesNotHold("""
                example boxedOf
                    | (1) -> Boxed { held = None }
                """);
    }

    @Test
    void aRecordReadsItsOwnInvariantToo() {
        // A construction's invariant is its own, as a newtype's is, and it is read of the value the
        // row wrote once every field states what this type declares it to be. Reading it only where
        // something was built through a decoder left it to whether that path happened to run.
        holds("""
                example widen
                    | (Span { from = 1, to = 1 }) -> Span { from = 1, to = 2 }
                """);
        assertTrue(couldNotBuild("""
                example widen
                    | (Span { from = 1, to = 2 }) -> Span { from = 5, to = 1 }
                """).contains("invariant"), "the row is told its own construction refused it");
    }

    @Test
    void anInvariantIsNotReadOfAValueTheRowDidNotWrite() {
        // The other half of the rule above, and the one that says which of the two a failure is.
        // `-1` at a `Decimal` field is an `Int`: the row wrote a value of another type, which is the
        // disagreement it reports. Reading it as the amount a boundary would have made of it and then
        // asking `at > 0m` would report a rule broken by a value nobody wrote.
        holds("""
                example pricedOf
                    | (1) -> Priced { at = 1m }
                """);
        refusedStatically("""
                example pricedOf
                    | (1) -> Priced { at = -1 }
                """, "E1317", "Decimal", "Int");
        // And the same reading, where no invariant is involved at all.
        refusedStatically("""
                example pricedOf
                    | (1) -> Priced { at = 1 }
                """, "E1317", "Decimal", "Int");
    }

    @Test
    void oneTemporalIsNotAnother() {
        // The four temporals were one written form to this reading, so a row could write any of them
        // where another stands. `Stamped` carries an invariant so the gate in front of it is the one
        // being asked: reading a `Date` as a value of a `DateTime` field is what would put it through
        // that field's decoder and report the row for a rule about a value it never wrote.
        holds("""
                example stampedOf
                    | (1) -> Stamped { from = DateTime("2026-07-20T09:00"),
                        to = DateTime("2026-07-21T09:00") }
                """);
        refusedStatically("""
                example stampedOf
                    | (1) -> Stamped { from = Date("2026-07-20"),
                        to = DateTime("2026-07-21T09:00") }
                """, "E1317", "DateTime", "Date");
    }

    @Test
    void aMapsKeysAreDistinct() {
        holds("""
                example codedOf
                    | (1) -> Coded { by = Map.fromList([("a", 1)]) }
                """);
        // Two entries under one key are `Map.fromList`'s to resolve, as they are in a body — a
        // row is not refused for them (a deliberate widening), and the map it states is compared.
        Diagnostic d = only("""
                example codedOf
                    | (1) -> Coded { by = Map.fromList([("a", 1), ("a", 2)]) }
                """);
        assertEquals("E1905", d.code(), d.said().toString());
    }

    @Test
    void aRecordStatesAValueForEveryFieldItHas() {
        // Leaving a field out is how an optional is written empty, and it is only that.
        holds("""
                example heldOf
                    | (1) -> Held { total = AmountN(1) }
                """);
        refusedStatically("""
                example receiptOf
                    | (1) -> Receipt { }
                """, "E1005", "total");
    }
}
