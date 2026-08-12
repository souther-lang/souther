package souther.compiler;

import souther.compiler.diag.CompileException;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An {@code example} row states its input, its expected result and its fake values by calling the
 * helper the rule is written in, rather than restating the rule's result as a literal (issue #200).
 * The helper is run and its result is brought back to the neutral form a fixture is written in, so
 * the row is still a fixture wherever the call stands.
 */
class ExampleCallsHelperTest {

    private static final String BASE = """
            module demo

            data Amount = Int

            data Receipt = { total: Amount }

            behavior bill : (a: Amount) -> Receipt
                constructs Receipt

            let bill (a) = Receipt { total = a }

            let taxed (a: Amount) = Amount(a.value * 11 / 10)
            """;

    private static final String INJECTED = """
            module demo

            data Amount = Int

            data Receipt = { total: Amount }

            behavior quote : (a: Amount) -> Amount

            behavior bill : (a: Amount) -> Receipt
                depends on quote
                constructs Receipt

            let bill (a, quote) = Receipt { total = quote(a) }

            let taxed (a: Amount) = Amount(a.value * 11 / 10)
            """;

    private static CompileException err(String model) {
        return assertThrows(CompileException.class, () -> Compiler.compile(model));
    }

    /** As {@link #err(String)}, for a model whose row does not come back: the same E1910, decided
     *  without waiting out a budget set for the rows that do. */
    private static CompileException errBriefly(String model) {
        return assertThrows(CompileException.class, () -> DoesNotComeBack.compile(model));
    }

    @Test
    void aHelperStatesTheInput() {
        assertDoesNotThrow(() -> Compiler.compile(BASE + """
                example bill
                  | (taxed(Amount(100))) -> Receipt { total = Amount(110) }
                """));
    }

    @Test
    void aHelperStatesTheExpectedResult() {
        assertDoesNotThrow(() -> Compiler.compile(BASE + """
                example bill
                  | (Amount(110)) -> Receipt { total = taxed(Amount(100)) }
                """));
    }

    @Test
    void aHelperStatesAFakeValue() {
        assertDoesNotThrow(() -> Compiler.compile(INJECTED + """
                example bill
                  | (Amount(1)) with quote = taxed(Amount(100)) -> Receipt { total = Amount(110) }
                """));
    }

    @Test
    void aRowThatDoesNotHoldStillFails() {
        // taxed(Amount(100)) is 110, not 120: the row is wrong and says so.
        assertTrue(err(BASE + """
                example bill
                  | (Amount(120)) -> Receipt { total = taxed(Amount(100)) }
                """).getMessage().contains("E1905"));
    }

    @Test
    void aHelperCallStandsWhereAFixtureValueStands() {
        // a record field, a list element, a map value and a map key
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Amount = Int
                data Sku = String
                data Cart = { lines: List<Amount>, prices: Map<Sku, Amount> }
                data Receipt = { cart: Cart }

                behavior bill : (c: Cart) -> Receipt
                    constructs Receipt

                let bill (c) = Receipt { cart = c }

                let taxed (a: Amount) = Amount(a.value * 11 / 10)

                let labelled (s: Sku) = Sku(s.value ++ "-x")

                example bill
                  | (Cart { lines = [ taxed(Amount(100)) ],
                            prices = [ (labelled(Sku("a")), taxed(Amount(200))) ] })
                      -> Receipt { cart = Cart { lines = [ Amount(110) ],
                                                 prices = [ (Sku("a-x"), Amount(220)) ] } }
                """));
    }

    @Test
    void aHelperCallIsAnArgumentOfAHelperCall() {
        assertDoesNotThrow(() -> Compiler.compile(BASE + """
                example bill
                  | (taxed(taxed(Amount(100)))) -> Receipt { total = Amount(121) }
                """));
    }

    @Test
    void aHelperThatCallsAHelperIsRun() {
        // `outer` reaches `inner`, which is expanded into it before it is emitted. Without that the
        // emitted method would call a method nothing emitted.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Amount = Int
                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt

                let bill (a) = Receipt { total = a }

                let rate = 11

                let scaled (a: Amount, by: Int) = Amount(a.value * by / 10)

                let taxed (a: Amount) = scaled(a, rate)

                example bill
                  | (taxed(Amount(100))) -> Receipt { total = Amount(110) }
                """));
    }

    @Test
    void aRecursiveHelperIsRun() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Amount = Int
                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt

                let bill (a) = Receipt { total = a }

                partial let sumTo (n: Int) : Int = if n <= 0 then 0 else n + sumTo(n - 1)

                partial let triangular (n: Int) = Amount(sumTo(n))

                example bill
                  | (triangular(4)) -> Receipt { total = Amount(10) }
                """));
    }

    @Test
    void oneRowMayCallTheSameHelperInEveryPosition() {
        assertDoesNotThrow(() -> Compiler.compile(INJECTED + """
                example bill
                  | (taxed(Amount(10))) with quote = taxed(Amount(100))
                      -> Receipt { total = taxed(Amount(100)) }
                """));
    }

    @Test
    void anArgumentThatBreaksAnInvariantIsAFixtureError() {
        CompileException e = err("""
                module demo

                data Amount = Int
                    invariant value > 0

                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt

                let bill (a) = Receipt { total = a }

                let taxed (a: Amount) = Amount(a.value * 11 / 10)

                example bill
                  | (taxed(Amount(0))) -> Receipt { total = Amount(0) }
                """);
        assertTrue(e.getMessage().contains("E1903"), e.getMessage());
    }

    @Test
    void aHelperReturningATemporalIsReadBack() {
        // A `Date`'s neutral form is the parsed temporal while its encoder writes ISO text, so this is
        // where re-materialising through the encoder alone would produce something the decoder cannot
        // read.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data LoanDate = Date
                data Loan = { on: LoanDate, due: Date }

                behavior record : (l: Loan) -> Loan

                let record (l) = l

                let nextDay (d: Date) = Date.addDays(1, d)

                let asLoanDate (d: Date) = LoanDate(d)

                example record
                  | (Loan { on = asLoanDate(Date("2026-07-30")), due = nextDay(Date("2026-07-30")) })
                      -> Loan { on = LoanDate(Date("2026-07-30")), due = Date("2026-07-31") }
                """));
    }

    @Test
    void aHelperReturningACollectionIsReadBack() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Label = String
                data Post = { labels: Set<Label>, counts: Map<Label, Int> }

                behavior publish : (p: Post) -> Post

                let publish (p) = p

                let labels (a: Label, b: Label) : Set<Label> = Set.fromList([ a, b ])

                let counted (a: Label) : Map<Label, Int> = Map.fromList([ (a, 1) ])

                example publish
                  | (Post { labels = labels(Label("bug"), Label("ui")), counts = counted(Label("bug")) })
                      -> Post { labels = [ Label("bug"), Label("ui") ], counts = [ (Label("bug"), 1) ] }
                """));
    }

    @Test
    void aHelperReturningACaseOfASumIsReadBack() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Amount = Int
                data Approved = { amount: Amount }
                data Refused
                data Decision = Approved | Refused

                behavior restate : (d: Decision) -> Decision

                let restate (d) = d

                let approve (a: Amount) : Decision = Approved { amount = a }

                let refuse (a: Amount) : Decision = Refused

                example restate
                  | (approve(Amount(100))) -> Approved { amount = Amount(100) }
                  | (refuse(Amount(0))) -> Refused
                """));
    }

    @Test
    void aHelperReturningARecordWithAnEmptyOptionalIsReadBack() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Note = String
                data Lead = { name: String, note: Note? }

                behavior keep : (l: Lead) -> Lead

                let keep (l) = l

                let unnoted (n: String) : Lead = Lead { name = n, note = None }

                let noted (n: String, note: Note) : Lead = Lead { name = n, note = note }

                example keep
                  | (unnoted("Acme")) -> Lead { name = "Acme" }
                  | (noted("Acme", Note("call back"))) -> Lead { name = "Acme", note = Note("call back") }
                """));
    }

    /**
     * An intrinsic a row applies is emitted as a method like any other helper the row applies
     * (issue #680). Which function a fixture may run is decided by the fixture's own rules, and not
     * by whether the backend happened to lower the function at its call sites.
     */
    @Test
    void aRowAppliesAnIntrinsic() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Amount = Int
                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt

                let bill (a) = Receipt { total = a }

                example bill
                  | (Amount(String.length("abc"))) -> Receipt { total = Amount(3) }
                """));
    }

    /** And the value is the one the intrinsic answers, not one the row was let state for itself. */
    @Test
    void aRowApplyingAnIntrinsicStillCatchesAMismatch() {
        CompileException e = err("""
                module demo

                data Amount = Int
                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt

                let bill (a) = Receipt { total = a }

                example bill
                  | (Amount(String.length("abc"))) -> Receipt { total = Amount(4) }
                """);
        assertEquals("E1905", e.diagnostic().code(), e.getMessage());
    }

    /**
     * A kernel the backend writes out as instructions rather than as a call to a runtime method is
     * applied too. What is emitted for the row is a method whose body is the one call, so whatever the
     * backend lowers that call to is what the row runs — a division writes a branch on a zero divisor,
     * and it writes it inside the method.
     */
    @Test
    void aRowAppliesAKernelTheBackendWritesOutInPlace() {
        assertDoesNotThrow(() -> Compiler.compile(INT_ROW + "  | (Int.divide(7, 2)) -> 3\n"));
    }

    /** The other arm of that branch, which is the half that makes these three kernels different from
     * the rest: the zero divisor answers a case, and the branch answering it is written inside the
     * emitted method like any other lowering. */
    @Test
    void theZeroDivisorBranchIsWrittenInsideTheEmittedMethodToo() {
        CompileException e = err(INT_ROW + "  | (Int.divide(7, 0)) -> 0\n");
        assertTrue(e.getMessage().contains("answered with a `DivisionByZero`"), e.getMessage());
    }

    /**
     * A kernel's method is emitted under a name no source can spell, and that name is where the method
     * went — not what the row applied. A report about a helper that did not answer names the helper,
     * so the wrapper's address does not reach the author (#680).
     */
    @Test
    void aKernelThatDoesNotAnswerIsNamedAsTheKernel() {
        CompileException e = err("""
                module demo

                behavior echoStr : (s: String) -> String

                let echoStr (s) = s

                example echoStr
                  | (String.slice(0, 99, "ab")) -> "ab"
                """);
        assertTrue(e.getMessage().contains("`String.slice` did not produce a value"), e.getMessage());
        assertTrue(!e.getMessage().contains("$intrinsic"),
                "the emitted method's name is not the helper's identity: " + e.getMessage());
    }

    private static final String INT_ROW = """
            module demo

            behavior echoInt : (n: Int) -> Int

            let echoInt (n) = n

            example echoInt
            """;

    /**
     * A library function whose parameter type is decided by each call is refused for that, whether it
     * is an intrinsic or written in Souther. The rule is the fixture's and reads the declaration, so
     * how the function is compiled does not enter (#692).
     */
    @Test
    void aPolymorphicIntrinsicIsRefusedForItsTypeVariable() {
        CompileException e = err("""
                module demo

                data Amount = Int
                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt

                let bill (a) = Receipt { total = a }

                example bill
                  | (Amount(List.length([ 1, 2 ]))) -> Receipt { total = Amount(2) }
                """);
        assertTrue(e.getMessage().contains("E1903"), e.getMessage());
        assertTrue(e.getMessage().contains("decided by each call"),
                "the type variable is the reason, not how `List.length` is compiled: " + e.getMessage());
        assertTrue(!e.getMessage().contains("standard-library"), e.getMessage());
    }

    /**
     * The other thing that reaches the same refusal. A helper whose body produces a function is not a
     * standard-library function, so it is not told to write the helper it already is — the sentence
     * this row holds is the one the intrinsic row above must not be given.
     */
    @Test
    void aHelperWhoseBodyProducesAFunctionIsRefusedByItsOwnReason() {
        CompileException e = err("""
                module demo

                let adder (n: Int) = m -> n + m

                behavior isThree : (n: Int) -> Bool

                let isThree (n) = n == 3

                example isThree
                  | (adder(1)) -> true
                """);
        assertTrue(e.getMessage().contains("no method was emitted for it"), e.getMessage());
        assertTrue(!e.getMessage().contains("standard-library"), e.getMessage());
    }

    @Test
    void aHelperWhoseElementEachCallDecidesCannotBuildAFixture() {
        // `count` compiles and runs at every element type, but a fixture is built before
        // there is a call to say which one — so the row is refused for the order, not for the type
        // being one the compiler does not support.
        CompileException e = err("""
                module demo

                data Amount = Int
                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt

                let bill (a) = Receipt { total = a }
                let count (xs) = List.length(xs)

                example bill
                  | (Amount(count([ 1, 2 ]))) -> Receipt { total = Amount(2) }
                """);
        assertTrue(e.getMessage().contains("E1903"), e.getMessage());
        assertTrue(e.getMessage().contains("decided by each call"),
                "the report says why a call works where a fixture does not: " + e.getMessage());
    }

    @Test
    void aValueWhoseBodyCallsAHelperIsAFixture() {
        assertDoesNotThrow(() -> Compiler.compile(BASE + """
                let standard = taxed(Amount(100))

                example bill
                  | (standard) -> Receipt { total = Amount(110) }
                """));
    }

    @Test
    void aRowThatDoesNotFinishLeavesTheRowsAfterItAlone() {
        // The worker evaluating a non-terminating row is not stopped by cancelling it — a pure
        // computation reaches no interrupt point — so it must share nothing with the rows after it: the
        // diagnostics stay in row order, and each row's own reason is its own.
        CompileException e = errBriefly("""
                module demo

                data Amount = Int
                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt

                let bill (a) = Receipt { total = a }

                partial let spin (n: Int) : Int = if n < 0 then 0 else spin(n + 1)

                partial let looping (n: Int) = Amount(spin(n))

                let taxed (a: Amount) = Amount(a.value * 110 / 100)

                example bill
                  | (looping(1)) -> Receipt { total = Amount(0) }
                  | (taxed(Amount(100))) -> Receipt { total = Amount(999) }
                """);

        assertEquals(2, e.diagnostics().size(), e.getMessage());
        assertEquals("E1910", e.diagnostics().get(0).code(), "the row that did not finish comes first");
        assertEquals("E1905", e.diagnostics().get(1).code(),
                "the row after it is compared, and its failure is its own");
    }

    @Test
    void aHelperThatDoesNotTerminateIsReportedAsNonTermination() {
        CompileException e = errBriefly("""
                module demo

                data Amount = Int
                data Receipt = { total: Amount }

                behavior bill : (a: Amount) -> Receipt
                    constructs Receipt

                let bill (a) = Receipt { total = a }

                partial let spin (n: Int) : Int = if n < 0 then 0 else spin(n + 1)

                partial let looping (n: Int) = Amount(spin(n))

                example bill
                  | (looping(1)) -> Receipt { total = Amount(0) }
                """);
        assertTrue(e.getMessage().contains("E1910"), e.getMessage());
    }
}
