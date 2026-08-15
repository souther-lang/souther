package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A fixture supplies a value of the type the position is written under, and says so itself.
 *
 * <p>What holds a row to the position's name is the one elaboration every definition goes through:
 * a row's operand is compiled as this module's code, against the type its position requires, so
 * another name over the same base, and no name at all, are refused the way they are refused in any
 * body — by the language's own type rules, at the position that mismatches. No decoder stands
 * between a row and the value it states, so there is nothing left that could supply a name the row
 * did not write.
 *
 * <p>Both ways round. A nominal position takes one of the names it holds; a primitive or a
 * collection takes a value under no name, since an `AmountN` is one wherever it is written and its
 * representation reading as an `Int` does not make it one.
 *
 * <p>Held at every position a value stands at rather than at the outermost one: a field of a record,
 * an element of a list, an argument of a helper, the value under a newtype and every position inside
 * what a helper answered with are each a position of their own.
 *
 * <p>An expected value is not held to any of it. A row may state what the behavior does not answer
 * with, and reporting that disagreement is what the row is for, so what a row expects is compared
 * rather than admitted.
 *
 * <p>What a spread supplies is not a value of the position: {@code Filed { ...d, filedOn = on }}
 * copies a {@code Document}'s fields, and holding {@code d} to being a {@code Filed} would refuse
 * the language's own way of writing one. So the frame a spread opens states no value of its own,
 * while every frame under it states one as any other does.
 */
class ADecoderMayNotSupplyANameAFixtureDidNotWriteTest {

    private static final String BASE = """
            module demo

            data Ok

            data AmountN = Int
            data AmountNN = AmountN
            data OtherAmountN = Int

            data A = { id: Int }
            data B = { id: Int }
            data S = A | B

            data Approved = { id: Int }
            data Rejected = { why: String }
            data Decision = Approved | Rejected
            data DecisionN = Decision

            data Order = { amount: AmountN }
            data Held = { amount: AmountN? }
            data IntList = List<Int>
            data Document = { amount: AmountN }
            data Filed = { amount: AmountN, filedOn: Date }

            behavior takesInt : (n: Int) -> Ok
                constructs Ok
            let takesInt (n) = Ok

            behavior takesAmount : (a: AmountN) -> Ok
                constructs Ok
            let takesAmount (a) = Ok

            behavior takesNested : (a: AmountNN) -> Ok
                constructs Ok
            let takesNested (a) = Ok

            behavior takesOrder : (o: Order) -> Ok
                constructs Ok
            let takesOrder (o) = Ok

            behavior takesMany : (a: List<AmountN>) -> Ok
                constructs Ok
            let takesMany (a) = Ok

            behavior takesIntList : (l: List<Int>) -> Ok
                constructs Ok
            let takesIntList (l) = Ok

            behavior takesSet : (s: Set<AmountN>) -> Ok
                constructs Ok
            let takesSet (s) = Ok

            behavior takesMap : (m: Map<String, AmountN>) -> Ok
                constructs Ok
            let takesMap (m) = Ok

            behavior takesHeld : (h: Held) -> Ok
                constructs Ok
            let takesHeld (h) = Ok

            behavior takesOk : (x: Ok) -> Ok
            let takesOk (x) = x

            behavior takesA : (a: A) -> Ok
                constructs Ok
            let takesA (a) = Ok

            behavior takesS : (s: S) -> Ok
                constructs Ok
            let takesS (s) = Ok

            behavior takesDecision : (d: DecisionN) -> Ok
                constructs Ok
            let takesDecision (d) = Ok

            behavior takesFiled : (f: Filed) -> Ok
                constructs Ok
            let takesFiled (f) = Ok

            behavior echo : (d: DecisionN) -> DecisionN
            let echo (d) = d

            behavior amountOf : (n: Int) -> AmountN
                constructs AmountN
            let amountOf (n) = AmountN(n)

            behavior orderOf : (n: Int) -> Order
                constructs Order, AmountN
            let orderOf (n) = Order { amount = AmountN(n) }

            let wrapped (n: Int): AmountN = AmountN(n)
            let bare (n: Int): Int = n
            let otherWrapped (n: Int): OtherAmountN = OtherAmountN(n)
            let inferredWrapped (n: Int) = AmountN(n)
            let inferredBare (n: Int) = n
            let identity (a: AmountN): AmountN = a
            let ints (n: Int): List<Int> = [n]
            let intSet (n: Int): Set<Int> = Set.fromList([n])
            let intMap (n: Int): Map<String, Int> = Map.fromList([("a", n)])
            let pickAmount (o: Held) = o.amount

            let doc: Document = Document { amount = AmountN(1) }
            let viaDoc: Document = doc
            let docOf (n: Int): Document = Document { amount = AmountN(n) }
            let builtDoc: Document = docOf(1)

            let full: Held = Held { amount = AmountN(1) }
            let empty: Held = Held { amount = None }
            """;

    /** A model whose rows all hold. */
    private static void admits(String rows) {
        Compiler.compile(BASE + rows);
    }

    /** The one diagnostic a model with one row states. */
    private static Diagnostic only(String rows) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(BASE + rows),
                "the row states no value of the position it is written at");
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        return e.diagnostics().get(0);
    }

    /**
     * The one diagnostic, held to the code the language answers with and to the names the row is
     * told. The code is the same rule's at the same position in a body — a row's operand is compiled
     * as this module's code, and the refusal is the type rule's, not a fixture reading's.
     */
    private static void refused(String rows, String code, String... names) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(BASE + rows),
                "the row states no value of the position it is written at");
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        assertEquals(code, e.diagnostics().get(0).code(), e.getMessage());
        for (String name : names) {
            assertTrue(e.getMessage().contains(name), "`" + name + "` is said: " + e.getMessage());
        }
    }

    @Test
    void aPrimitivePositionAsksForNoName() {
        admits("""
                example takesInt
                    | (1) -> Ok
                """);
    }

    @Test
    void aNewtypeIsWrittenUnderItsOwnName() {
        admits("""
                example takesAmount
                    | (AmountN(1)) -> Ok
                """);
    }

    @Test
    void aNewtypePositionRefusesAValueWithNoNameOverIt() {
        refused("""
                example takesAmount
                    | (1) -> Ok
                """, "E1812", "AmountN", "Int");
    }

    @Test
    void aNewtypePositionRefusesAnotherNameOverTheSameBase() {
        refused("""
                example takesAmount
                    | (OtherAmountN(1)) -> Ok
                """, "E1812", "AmountN", "OtherAmountN");
    }

    @Test
    void aHelperAnsweringWithTheNameSuppliesIt() {
        admits("""
                example takesAmount
                    | (wrapped(1)) -> Ok
                """);
    }

    @Test
    void aHelperAnsweringWithTheBaseDoesNot() {
        refused("""
                example takesAmount
                    | (bare(1)) -> Ok
                """, "E1812", "AmountN", "Int");
    }

    @Test
    void aHelperAnsweringWithAnotherNameDoesNot() {
        refused("""
                example takesAmount
                    | (otherWrapped(1)) -> Ok
                """, "E1812", "AmountN", "OtherAmountN");
    }

    @Test
    void whatAHelperAnsweredWithIsReadAndNotItsDeclaration() {
        admits("""
                example takesAmount
                    | (inferredWrapped(1)) -> Ok
                """);
        refused("""
                example takesAmount
                    | (inferredBare(1)) -> Ok
                """, "E1812", "AmountN", "Int");
    }

    @Test
    void aNestedNewtypeIsWrittenOutInFull() {
        admits("""
                example takesNested
                    | (AmountNN(AmountN(1))) -> Ok
                """);
    }

    @Test
    void aNestedNewtypeRefusesALayerLeftOff() {
        refused("""
                example takesNested
                    | (AmountN(1)) -> Ok
                """, "E1812", "AmountNN", "AmountN");
        refused("""
                example takesNested
                    | (1) -> Ok
                """, "E1812", "AmountNN", "Int");
    }

    @Test
    void aFieldIsAPositionOfItsOwn() {
        admits("""
                example takesOrder
                    | (Order { amount = AmountN(1) }) -> Ok
                """);
        refused("""
                example takesOrder
                    | (Order { amount = 1 }) -> Ok
                """, "E1317", "AmountN", "Int");
        refused("""
                example takesOrder
                    | (Order { amount = OtherAmountN(1) }) -> Ok
                """, "E1317", "AmountN", "OtherAmountN");
    }

    @Test
    void anElementIsAPositionOfItsOwn() {
        admits("""
                example takesMany
                    | ([AmountN(1), AmountN(2)]) -> Ok
                """);
        refused("""
                example takesMany
                    | ([AmountN(1), 2]) -> Ok
                """, "E1318", "AmountN");
    }

    @Test
    void anArgumentOfAnAppliedHelperIsAPositionOfItsOwn() {
        admits("""
                example takesAmount
                    | (identity(AmountN(1))) -> Ok
                """);
        refused("""
                example takesAmount
                    | (identity(1)) -> Ok
                """, "E1317", "AmountN", "Int");
    }

    @Test
    void aRecordPositionRefusesARecordOfTheSameShape() {
        admits("""
                example takesA
                    | (A { id = 1 }) -> Ok
                """);
        refused("""
                example takesA
                    | (B { id = 1 }) -> Ok
                """, "E1812", "A", "B");
    }

    @Test
    void aSumPositionTakesAnyOfItsCases() {
        admits("""
                example takesS
                    | (A { id = 1 }) -> Ok
                    | (B { id = 2 }) -> Ok
                """);
    }

    @Test
    void aNewtypeOverASumIsWrittenUnderItsOwnNameToo() {
        admits("""
                example takesDecision
                    | (DecisionN(Approved { id = 1 })) -> Ok
                """);
        refused("""
                example takesDecision
                    | (Approved { id = 1 }) -> Ok
                """, "E1812", "DecisionN", "Approved");
    }

    @Test
    void whatWasAdmittedIsWhatTheBehaviourRunsOn() {
        admits("""
                example echo
                    | (DecisionN(Approved { id = 1 })) -> DecisionN(Approved { id = 1 })
                """);
    }

    @Test
    void anExpectedValueIsComparedAndNotAdmitted() {
        // Where the rule stops. A row may state what the behavior does not answer with, and reporting
        // that disagreement is what the row is for, so an expected value is built and compared rather
        // than held to its position — a number expected where an `AmountN` comes out is a mismatch
        // the row reports (E1905) and not a fixture that could not be built.
        admits("""
                example amountOf
                    | (1) -> AmountN(1)
                """);
        assertEquals("E1905", only("""
                example amountOf
                    | (1) -> 1
                """).code());
        assertEquals("E1905", only("""
                example amountOf
                    | (1) -> bare(1)
                """).code());
    }

    @Test
    void aPositionThatWearsNoNameRefusesOne() {
        // The rule read the other way. A `data AmountN = Int` is an `AmountN` wherever it is written,
        // and its representation reading as an `Int` does not make it one.
        refused("""
                example takesInt
                    | (AmountN(1)) -> Ok
                """, "E1812", "Int", "AmountN");
        refused("""
                example takesIntList
                    | (IntList([1])) -> Ok
                """, "E1812", "List<Int>", "IntList");
        refused("""
                example takesAmount
                    | (AmountN(OtherAmountN(1))) -> Ok
                """, "E1317", "Int", "OtherAmountN");
    }

    @Test
    void aHelperAnswersForEveryPositionInsideWhatItAnsweredWith() {
        admits("""
                example takesMany
                    | ([AmountN(1)]) -> Ok
                """);
        refused("""
                example takesMany
                    | (ints(1)) -> Ok
                """, "E1812", "List<AmountN>", "List<Int>");
        refused("""
                example takesSet
                    | (intSet(1)) -> Ok
                """, "E1812", "Set<AmountN>", "Set<Int>");
        refused("""
                example takesMap
                    | (intMap(1)) -> Ok
                """, "E1812", "Map<String, AmountN>", "Map<String, Int>");
    }

    @Test
    void anOptionalTakesWhatItHoldsAndAbsence() {
        admits("""
                example takesHeld
                    | (Held { amount = AmountN(1) }) -> Ok
                    | (Held { amount = None }) -> Ok
                    | (Held { amount = pickAmount(full) }) -> Ok
                    | (Held { amount = pickAmount(empty) }) -> Ok
                """);
        refused("""
                example takesHeld
                    | (Held { amount = 1 }) -> Ok
                """, "E1317", "AmountN");
    }

    @Test
    void absenceStandsWhereAnOptionalMakesRoomForItAndNowhereElse() {
        // `None` is the empty value of a `?` position, and none of these is one. The refusal is the
        // language's (E1303), whose sentence is about where absence may stand — it does not need to
        // name the position's type to refuse standing anywhere else.
        refused("""
                example takesOk
                    | (None) -> Ok
                """, "E1303");
        refused("""
                example takesAmount
                    | (None) -> Ok
                """, "E1303");
        refused("""
                example takesInt
                    | (None) -> Ok
                """, "E1303");
    }

    @Test
    void aSpreadSuppliesFieldsAndNotAValueOfThePosition() {
        admits("""
                example takesFiled
                    | (Filed { ...doc, filedOn = Date("2026-01-01") }) -> Ok
                """);
    }

    @Test
    void aSpreadStatesNoValueHoweverItsSourceIsReached() {
        // The exemption is the frame's, and a name and an application go on at that same frame: they
        // stand for what the spread names rather than opening a position of their own.
        admits("""
                example takesFiled
                    | (Filed { ...viaDoc, filedOn = Date("2026-01-01") }) -> Ok
                """);
        admits("""
                example takesFiled
                    | (Filed { ...builtDoc, filedOn = Date("2026-01-01") }) -> Ok
                """);
    }

    @Test
    void aFieldWrittenBesideASpreadIsStillAPosition() {
        refused("""
                example takesFiled
                    | (Filed { ...doc, amount = 1, filedOn = Date("2026-01-01") }) -> Ok
                """, "E1317", "AmountN", "Int");
    }
}
