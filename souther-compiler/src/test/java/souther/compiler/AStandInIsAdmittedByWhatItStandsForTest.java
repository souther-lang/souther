package souther.compiler;

import souther.compiler.diag.msg.ExampleMessage;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;

/**
 * A stand-in states what a dependency answers with, so it holds to the dependency's declared output.
 * A value of another type is refused where it is written, before anything runs, so no row reaches the
 * model holding one and no cast failure can be what an example reports.
 *
 * <p>An expected value is built the way the row wrote it, because a row is allowed to state a case
 * the behavior does not answer with — that disagreement is what it reports. A stand-in has no such
 * licence: it is the dependency's answer while the row runs.
 */
class AStandInIsAdmittedByWhatItStandsForTest {

    private static final String TEMPORAL = """
            module repro exposing ( Stamp, Mark, Moment, now, stampAt )

            data Stamp = { at: DateTime }
            data Mark = { on: Date }
            data Moment = DateTime

            behavior now : () -> DateTime

            behavior stampAt : () -> Stamp
                depends on now
                constructs Stamp
            let stampAt (now) = Stamp { at = now() }
            """;

    private static final String UNION = """
            module answers exposing ( Ok, No, Other, Answer, Wrapped, ask, run )

            data Ok = { n: Int }
            data No = { n: Int }
            data Other = { n: Int }
            data Answer = Ok | No
            data Wrapped = { a: Answer }

            behavior ask : () -> Answer

            behavior run : () -> Wrapped
                depends on ask
                constructs Wrapped
            let run (ask) = Wrapped { a = ask() }
            """;

    private static final String INLINE_UNION = """
            module inline exposing ( Ok, No, Other, ask, run )

            data Ok = { n: Int }
            data No = { n: Int }
            data Other = { n: Int }

            behavior ask : () -> Ok | No

            behavior run : () -> Ok | No
                depends on ask
            let run (ask) = ask()
            """;

    private static final String NEWTYPE = """
            module money exposing ( Amount, Receipt, quote, bill )

            data Amount = Int
            data Receipt = { total: Amount }

            behavior quote : (a: Amount) -> Amount

            behavior bill : (a: Amount) -> Receipt
                depends on quote
                constructs Receipt
            let bill (a, quote) = Receipt { total = quote(a) }
            """;

    private static final String COLLECTION = """
            module bags exposing ( Bag, sizes, hold )

            data Bag = { ns: List<Int> }

            behavior sizes : () -> List<Int>

            behavior hold : () -> Bag
                depends on sizes
                constructs Bag
            let hold (sizes) = Bag { ns = sizes() }
            """;

    private static Diagnostic only(String model) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(model));
        assertEquals(1, e.diagnostics().size(), "one row, one diagnostic: " + e.getMessage());
        return e.diagnostics().get(0);
    }

    private static void refusedAsAStandIn(String model, Class<? extends ExampleMessage> said) {
        Diagnostic d = only(model);
        assertEquals("E1908", d.code(), "a stand-in that does not stand for the dependency's output"
                + " is the stand-in's error, not the row's result: " + d.said());
        assertInstanceOf(said, d.said());
    }

    // --- a `with` value, per output shape -------------------------------------------------------

    @Test
    void aWithOfAnotherScalarDoesNotStandInForTheDependency() {
        refusedAsAStandIn(TEMPORAL + """

                example stampAt
                    | "a date" : () with now = Date("2026-07-20") -> Stamp
                """, ExampleMessage.TheFakeValueCouldNotBeBuilt.class);
    }

    @Test
    void aWithOfAnotherRecordDoesNotStandInForTheDependency() {
        refusedAsAStandIn(TEMPORAL + """

                example stampAt
                    | "a record" : () with now = Mark { on = Date("2026-07-20") } -> Stamp
                """, ExampleMessage.TheFakeValueCouldNotBeBuilt.class);
    }

    @Test
    void aWithOfANewtypeOverTheOutputIsNotTheOutput() {
        // `Moment` wraps `DateTime`, so it carries what the dependency answers with and is still not
        // it: a nominal type is the type it was declared as, not the one it is represented by.
        refusedAsAStandIn(TEMPORAL + """

                example stampAt
                    | "a newtype" : () with now = Moment(DateTime("2026-07-20T09:00")) -> Stamp
                """, ExampleMessage.TheFakeValueCouldNotBeBuilt.class);
    }

    @Test
    void aWithOfACaseOutsideTheOutputsUnionDoesNotStandInForIt() {
        // The expected side reports this as E1904. A stand-in has no case to compare against — it is
        // the answer — so what is wrong with it is that it cannot be one.
        refusedAsAStandIn(UNION + """

                example run
                    | "outside" : () with ask = Other { n = 1 } -> Wrapped { a = Ok { n = 1 } }
                """, ExampleMessage.TheFakeValueCouldNotBeBuilt.class);
    }

    @Test
    void aWithOfACaseOutsideAnUnnamedUnionDoesNotStandInForIt() {
        // An answer of several types has no one decoder to be admitted by, so what admits a value
        // here is being one of the cases rather than being represented as one shape.
        refusedAsAStandIn(INLINE_UNION + """

                example run
                    | "outside" : () with ask = Other { n = 1 } -> Ok { n = 1 }
                """, ExampleMessage.TheFakeValueCouldNotBeBuilt.class);
    }

    @Test
    void aStandInNamingACaseOfAnUnnamedUnionStillStandsIn() {
        assertDoesNotThrow(() -> Compiler.compile(INLINE_UNION + """

                example run
                    | "a case of the union" : () with ask = Ok { n = 1 } -> Ok { n = 1 }
                """));
    }

    @Test
    void aWithHoldingAnotherElementTypeDoesNotStandInForACollectionOutput() {
        // The container is the one the dependency answers with and what it holds is not, so being a
        // `List` is not being this one. A helper answers here because a written list would be read
        // through the output's own element type and never arrive holding anything else.
        refusedAsAStandIn(COLLECTION + """

                let texts (s: String) : List<String> = [ s ]

                example hold
                    | "another element" : () with sizes = texts("a") -> Bag { ns = [ 1 ] }
                """, ExampleMessage.TheFakeValueCouldNotBeBuilt.class);
    }

    @Test
    void aWithHoldingTheOutputsElementTypeStandsInForACollectionOutput() {
        assertDoesNotThrow(() -> Compiler.compile(COLLECTION + """

                let ns (n: Int) : List<Int> = [ n ]

                example hold
                    | "the output's element" : () with sizes = ns(1) -> Bag { ns = [ 1 ] }
                """));
    }

    // --- a `fake` table's output ----------------------------------------------------------------

    @Test
    void aFakeOutputOfAnotherTypeDoesNotStandInForTheDependency() {
        refusedAsAStandIn(NEWTYPE + """

                fake quote
                    | (Amount(1)) -> Receipt { total = Amount(1) }

                example bill
                    | "wrong output" : (Amount(1)) -> Receipt { total = Amount(1) }
                """, ExampleMessage.TheFakeCouldNotBeBuilt.class);
    }

    @Test
    void aFakeDefaultOutputOfAnotherTypeDoesNotStandInForTheDependency() {
        refusedAsAStandIn(NEWTYPE + """

                fake quote
                    | _ -> Receipt { total = Amount(1) }

                example bill
                    | "wrong default" : (Amount(1)) -> Receipt { total = Amount(1) }
                """, ExampleMessage.TheFakeCouldNotBeBuilt.class);
    }

    // --- what a stand-in may still be written as ------------------------------------------------

    @Test
    void aBaseLiteralStillBuildsTheNewtypeTheDependencyAnswersWith() {
        // What an input position admits, a stand-in admits: a newtype's derived decoder reads its
        // base representation, and `2` is how an `Amount` is written where the type is known.
        assertDoesNotThrow(() -> Compiler.compile(NEWTYPE + """

                example bill
                    | "a base literal" : (Amount(1)) with quote = 2 -> Receipt { total = Amount(2) }
                """));
    }

    @Test
    void aHelperAnsweringForTheWholeStandInStillStandsIn() {
        // The value a helper answered with is already built, and reading it back through the output's
        // decoder would state nothing for a stand-in written as an application.
        assertDoesNotThrow(() -> Compiler.compile(NEWTYPE + """

                let doubled (a: Amount) = Amount(a.value * 2)

                example bill
                    | "a helper" : (Amount(1)) with quote = doubled(Amount(1))
                        -> Receipt { total = Amount(2) }
                """));
    }

    @Test
    void aStandInOfTheDependencysOwnOutputStillStandsIn() {
        assertDoesNotThrow(() -> Compiler.compile(TEMPORAL + """

                example stampAt
                    | "the output's own form" : () with now = DateTime("2026-07-20T09:00") -> Stamp
                """));
    }

    @Test
    void aStandInNamingACaseOfTheOutputsUnionStillStandsIn() {
        assertDoesNotThrow(() -> Compiler.compile(UNION + """

                example run
                    | "a case of the union" : () with ask = Ok { n = 1 }
                        -> Wrapped { a = Ok { n = 1 } }
                """));
    }
}
