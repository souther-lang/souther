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
 * A fixture supplies a value of the type the position is written under, and says so itself.
 *
 * <p>A derived decoder reads the form its base reads and wraps what it read in its own name, so the
 * name a position is written under is one the decoder supplies: another name over the same base, and
 * no name at all, reach it as the one form. What holds a row to that name is read before anything
 * reaches a decoder — the name the row wrote, or, where a helper answered, the value it answered
 * with.
 *
 * <p>Held at every position a value stands at rather than at the outermost one: a field of a record,
 * an element of a list, an argument of a helper and the value under a newtype are each a position of
 * their own.
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

            let doc: Document = Document { amount = AmountN(1) }
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
        Diagnostic d = e.diagnostics().get(0);
        assertEquals("E1903", d.code(), d.said().toString());
        return d;
    }

    /** What the row was told, where an input could not be built. */
    private static String refuses(String rows) {
        return assertInstanceOf(ExampleMessage.AnInputCouldNotBeBuilt.class, only(rows).said()).why();
    }

    /** The same, where the expected value could not be built. */
    private static String refusesExpected(String rows) {
        return assertInstanceOf(ExampleMessage.TheExpectedValueCouldNotBeBuilt.class,
                only(rows).said()).why();
    }

    /** Both names, so the row is told which one it is written under and which one it wrote. */
    private static void names(String why, String position, String written) {
        assertTrue(why.contains("`" + position + "`"),
                "the name the position is written under: " + why);
        assertTrue(why.contains("`" + written + "`"), "the name the row wrote: " + why);
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
        String why = refuses("""
                example takesAmount
                    | (1) -> Ok
                """);
        assertTrue(why.contains("`AmountN`"), why);
    }

    @Test
    void aNewtypePositionRefusesAnotherNameOverTheSameBase() {
        names(refuses("""
                example takesAmount
                    | (OtherAmountN(1)) -> Ok
                """), "AmountN", "OtherAmountN");
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
        assertTrue(refuses("""
                example takesAmount
                    | (bare(1)) -> Ok
                """).contains("`AmountN`"));
    }

    @Test
    void aHelperAnsweringWithAnotherNameDoesNot() {
        names(refuses("""
                example takesAmount
                    | (otherWrapped(1)) -> Ok
                """), "AmountN", "OtherAmountN");
    }

    @Test
    void whatAHelperAnsweredWithIsReadAndNotItsDeclaration() {
        admits("""
                example takesAmount
                    | (inferredWrapped(1)) -> Ok
                """);
        assertTrue(refuses("""
                example takesAmount
                    | (inferredBare(1)) -> Ok
                """).contains("`AmountN`"));
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
        names(refuses("""
                example takesNested
                    | (AmountN(1)) -> Ok
                """), "AmountNN", "AmountN");
        assertTrue(refuses("""
                example takesNested
                    | (1) -> Ok
                """).contains("`AmountNN`"));
    }

    @Test
    void aFieldIsAPositionOfItsOwn() {
        admits("""
                example takesOrder
                    | (Order { amount = AmountN(1) }) -> Ok
                """);
        assertTrue(refuses("""
                example takesOrder
                    | (Order { amount = 1 }) -> Ok
                """).contains("`AmountN`"));
        names(refuses("""
                example takesOrder
                    | (Order { amount = OtherAmountN(1) }) -> Ok
                """), "AmountN", "OtherAmountN");
    }

    @Test
    void anElementIsAPositionOfItsOwn() {
        admits("""
                example takesMany
                    | ([AmountN(1), AmountN(2)]) -> Ok
                """);
        assertTrue(refuses("""
                example takesMany
                    | ([AmountN(1), 2]) -> Ok
                """).contains("`AmountN`"));
    }

    @Test
    void anArgumentOfAnAppliedHelperIsAPositionOfItsOwn() {
        admits("""
                example takesAmount
                    | (identity(AmountN(1))) -> Ok
                """);
        assertTrue(refuses("""
                example takesAmount
                    | (identity(1)) -> Ok
                """).contains("`AmountN`"));
    }

    @Test
    void aRecordPositionRefusesARecordOfTheSameShape() {
        admits("""
                example takesA
                    | (A { id = 1 }) -> Ok
                """);
        names(refuses("""
                example takesA
                    | (B { id = 1 }) -> Ok
                """), "A", "B");
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
        names(refuses("""
                example takesDecision
                    | (Approved { id = 1 }) -> Ok
                """), "DecisionN", "Approved");
    }

    @Test
    void whatWasAdmittedIsWhatTheBehaviourRunsOn() {
        admits("""
                example echo
                    | (DecisionN(Approved { id = 1 })) -> DecisionN(Approved { id = 1 })
                """);
    }

    @Test
    void anExpectedValueIsWrittenAtItsPositionToo() {
        // A row may expect a case the behavior does not answer with, which is a disagreement it
        // reports. Which name the value is written under is not that: a number states no `AmountN`,
        // so there is nothing to disagree about and the row is told what it wrote.
        admits("""
                example amountOf
                    | (1) -> AmountN(1)
                """);
        assertTrue(refusesExpected("""
                example amountOf
                    | (1) -> 1
                """).contains("`AmountN`"));
        admits("""
                example orderOf
                    | (1) -> Order { amount = AmountN(1) }
                """);
        assertTrue(refusesExpected("""
                example orderOf
                    | (1) -> Order { amount = 1 }
                """).contains("`AmountN`"));
    }

    @Test
    void aSpreadSuppliesFieldsAndNotAValueOfThePosition() {
        admits("""
                example takesFiled
                    | (Filed { ...doc, filedOn = Date("2026-01-01") }) -> Ok
                """);
    }

    @Test
    void aFieldWrittenBesideASpreadIsStillAPosition() {
        assertTrue(refuses("""
                example takesFiled
                    | (Filed { ...doc, amount = 1, filedOn = Date("2026-01-01") }) -> Ok
                """).contains("`AmountN`"));
    }
}
