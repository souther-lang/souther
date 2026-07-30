package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A fixture built by a spread is a construction of the case it names. The spread copies the fields of
 * the value it names, and the discriminator its sum's decoder reads is not one of them — so the case
 * comes from the construction that writes it, wherever the fixture is written and however deep the
 * chain of spreads goes.
 *
 * <p>It used to come from the spread source: the source's own neutral form carries its tag, copying
 * every entry brought the tag along, and the enclosing construction's tag was then never written. Where
 * the position is a union that decides which case the behavior sees, so a row ran against the wrong
 * case — reporting a mismatch that named the right expectation and the wrong actual, or passing where
 * both cases answer alike (issue #206).
 */
class ExampleSpreadFixtureTest {

    private static final String DEALS = """
            data Common = { id: String }
            data Open   = { ...Common }
            data Closed = { ...Common, closedOn: Date }
            data Deal   = Open | Closed
            data Answer = { label: String }

            behavior labelOf : (deal: Deal) -> Answer
                constructs Answer

            let labelOf (deal) =
                match deal with
                    | Open   -> Answer { label = "open" }
                    | Closed -> Answer { label = "closed" }
            """;

    @Test
    void aValueBuiltByASpreadKeepsItsOwnCase() {
        assertDoesNotThrow(() -> Compiler.compile("module demo\n" + DEALS + """

                let openDeal     = Open { id = "d-1" }
                let spreadClosed = Closed { ...openDeal, closedOn = Date("2026-07-30") }

                example labelOf
                    | "a flat fixture keeps its case"
                        : (Closed { id = "d-1", closedOn = Date("2026-07-30") }) -> Answer { label = "closed" }
                    | "a fixture built by a spread keeps its case"
                        : (spreadClosed) -> Answer { label = "closed" }
                    | "the row writing the case around it"
                        : (Closed { ...spreadClosed }) -> Answer { label = "closed" }
                """));
    }

    @Test
    void aRowSpreadingAValueOfAnotherCaseKeepsTheCaseItWrites() {
        assertDoesNotThrow(() -> Compiler.compile("module demo\n" + DEALS + """

                let openDeal = Open { id = "d-1" }

                example labelOf
                    | "a row spreading a flat value into a union position"
                        : (Closed { ...openDeal, closedOn = Date("2026-07-30") }) -> Answer { label = "closed" }
                """));
    }

    @Test
    void aChainOfSpreadsKeepsTheCaseTheOutermostConstructionWrites() {
        assertDoesNotThrow(() -> Compiler.compile("module demo\n" + DEALS + """

                let openDeal     = Open { id = "d-1" }
                let spreadClosed = Closed { ...openDeal, closedOn = Date("2026-07-30") }
                let reSpread     = Closed { ...spreadClosed }

                example labelOf
                    | "a spread of a spread" : (reSpread) -> Answer { label = "closed" }
                """));
    }

    @Test
    void anImportedValueBuiltByASpreadIsAFixture() {
        // A published value arrives closed over its own module, which binds what its spread names ahead
        // of the construction. A fixture reads that binding, so a value another module built by a
        // spread can be named by a row here.
        String deals = """
                module deals exposing ( Common, Open, Closed, Deal, spreadClosed )

                data Common = { id: String }
                data Open   = { ...Common }
                data Closed = { ...Common, closedOn: Date }
                data Deal   = Open | Closed

                let openDeal     = Open { id = "d-1" }
                let spreadClosed = Closed { ...openDeal, closedOn = Date("2026-07-30") }
                """;
        String app = """
                module app
                import deals ( Deal, Open, Closed, spreadClosed )

                data Answer = { label: String }

                behavior labelOf : (deal: Deal) -> Answer
                    constructs Answer

                let labelOf (deal) =
                    match deal with
                        | Open   -> Answer { label = "open" }
                        | Closed -> Answer { label = "closed" }

                example labelOf
                    | "an imported value built by a spread" : (spreadClosed) -> Answer { label = "closed" }
                """;
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(deals, app)));
    }

    @Test
    void aSpreadFixtureStillHasToHold() {
        // The case a spread fixture keeps is not a way past the check: a row asserting the other case
        // fails, and it is the row that is wrong rather than the fixture.
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile("module demo\n" + DEALS + """

                        let openDeal     = Open { id = "d-1" }
                        let spreadClosed = Closed { ...openDeal, closedOn = Date("2026-07-30") }

                        example labelOf
                            | "wrong" : (spreadClosed) -> Answer { label = "open" }
                        """));
        assertEquals("E1905", e.diagnostic().code());
    }

    @Test
    void aSpreadOfACaseOfAnotherSumIsStillTheCaseTheConstructionWrites() {
        // The other face of the same thing: where the source's case is no case of the position's union,
        // the tag it brought was not one the decoder accepts, so the row was refused rather than run
        // against the wrong case. Each state of a pipeline is written as the one before it plus what
        // that stage agreed, which is exactly this shape.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Submitted = { id: String, submittedOn: Date }
                data Withdrawn = { id: String }
                data Request   = Submitted | Withdrawn

                data Approved = { id: String, submittedOn: Date, approvedOn: Date }
                data Refused  = { id: String, why: String }
                data Decision = Approved | Refused

                data Answer = { label: String }

                behavior labelOf : (decision: Decision) -> Answer
                    constructs Answer

                let labelOf (decision) =
                    match decision with
                        | Approved -> Answer { label = "approved" }
                        | Refused  -> Answer { label = "refused" }

                let submitted = Submitted { id = "r-1", submittedOn = Date("2026-07-29") }

                example labelOf
                    | "the state after it is this state plus what the stage agreed"
                        : (Approved { ...submitted, approvedOn = Date("2026-07-30") })
                            -> Answer { label = "approved" }
                """));
    }

    @Test
    void aSpreadCopiesOnlyTheFieldsTheConstructionHas() {
        // The language lets a spread bring a value with a field the construction does not declare, and
        // drops it. A fixture is built the same way, so the row holds rather than handing the decoder a
        // key nothing declared.
        assertDoesNotThrow(() -> Compiler.compile("""
                module demo

                data Wide   = { id: String, extra: Int }
                data Narrow = { id: String }
                data Answer = { label: String }

                let wide   = Wide { id = "x", extra = 1 }
                let narrow = Narrow { ...wide }

                behavior labelOf : (v: Narrow) -> Answer
                    constructs Answer

                let labelOf (v) = Answer { label = v.id }

                example labelOf
                    | "an extra field is not copied" : (narrow) -> Answer { label = "x" }
                """));
    }
}
