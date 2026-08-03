package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Located;
import souther.compiler.meta.ModulePath;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code fake} and an {@code example} row are two statements about what one behavior answers,
 * written independently: the rows say what it will owe, the fake says what it stands in with while
 * some other behavior's row runs. Where both answer one input and answer it differently, that is
 * said — at both of the places it is written, and with neither named as the right one. A model being
 * migrated onto may run against a stand-in while the real answer is still being harvested, which is
 * written here exactly as a mistake is.
 */
class CompileFakeExampleDisagreementTest {

    private static final String BASE = """
            module example.clash

            data MemberId = String
            data Found = { id: MemberId }
            data Missing = { why: String }

            data Order = { by: MemberId }
            data Placed = { by: MemberId }
            data Refused = { why: String }

            behavior findMember : (id: MemberId) -> Found | Missing

            behavior place : (order: Order) -> Placed | Refused
                depends on findMember
                constructs Placed, Refused

            let place (order, findMember) = match findMember(order.by) with
                | Found    -> Placed { by = order.by }
                | Missing  -> Refused { why = "unknown" }
            """;

    /** The E1919s of a single-source compile, in the order they were said. */
    private static List<Located> disagreements(String model) {
        List<Located> out = new ArrayList<>();
        assertDoesNotThrow(() -> Compiler.compiled(model, "Main", out));
        return onlyDisagreements(out);
    }

    private static List<Located> onlyDisagreements(List<Located> warnings) {
        List<Located> found = new ArrayList<>();
        for (Located w : warnings) {
            if ("E1919".equals(w.diagnostic().code())) {
                found.add(w);
            }
        }
        return found;
    }

    private static boolean anyDisagreement(String model) {
        return !disagreements(model).isEmpty();
    }

    // --- a fake row and a recorded row --------------------------------------------------------

    @Test
    void aFakeAndARowThatAnswerOneInputDifferentlyAreSaidAtBoth() {
        List<Located> found = disagreements(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | (MemberId("m-1")) -> Missing { why = "no such member" }

                example place
                    | "m-1 cannot order" : (Order { by = MemberId("m-1") }) -> Refused { why = "unknown" }
                """);

        // One disagreement, said at the row and at the fake row: both are written statements, and
        // which of them is right is not what this reports.
        assertEquals(2, found.size(), found.toString());
        List<Integer> lines = new ArrayList<>();
        for (Located w : found) {
            lines.add(w.diagnostic().pos().line());
        }
        assertEquals(List.of(22, 25), lines, "the row, then the fake row");
    }

    @Test
    void aFakeAndARowThatAgreeSayNothing() {
        assertFalse(anyDisagreement(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | (MemberId("m-1")) -> Found { id = MemberId("m-1") }
                """));
    }

    @Test
    void aRowIsStillHeldAgainstAStaleFakeOnceTheLetArrives() {
        // `findMember` is implemented here, so its rows are run rather than recorded — and the fake
        // beside them is still a second statement about what it answers.
        assertTrue(anyDisagreement("""
                module example.clash

                data MemberId = String
                data Found = { id: MemberId }
                data Missing = { why: String }

                behavior findMember : (id: MemberId) -> Found | Missing
                    constructs Found

                let findMember (id) = Found { id = id }

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | (MemberId("m-1")) -> Missing { why = "no such member" }
                """));
    }

    // --- what a fake actually answers for the input -------------------------------------------

    @Test
    void aDefaultRowAnswersAnInputNoExplicitRowStates() {
        // The default is what the fake answers `m-1` with, so it is what `m-1`'s recorded row is
        // held against — the fake's own dispatch decides which row stands in, not the shape of it.
        assertTrue(anyDisagreement(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | _ -> Missing { why = "no such member" }
                """));
    }

    @Test
    void anExplicitRowIsWhatAnswersWhereOneStatesTheInput() {
        assertFalse(anyDisagreement(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | (MemberId("m-1")) -> Found { id = MemberId("m-1") }
                    | _ -> Missing { why = "no such member" }
                """));
    }

    @Test
    void aTableThatAnswersNothingForTheInputSaysNothing() {
        assertFalse(anyDisagreement(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | (MemberId("m-9")) -> Missing { why = "no such member" }
                """));
    }

    @Test
    void aSecondTableForOneDependencyStandsInForNothing() {
        // The first table is the one that answers, so the second states nothing to disagree with.
        List<Located> found = disagreements(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | (MemberId("m-1")) -> Missing { why = "no such member" }
                """);

        assertEquals(0, found.size(), found.toString());
    }

    // --- a row that names only a case ---------------------------------------------------------

    @Test
    void aRowThatNamesOnlyACaseIsComparedOnTheCase() {
        assertTrue(anyDisagreement(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found

                fake findMember
                    | (MemberId("m-1")) -> Missing { why = "no such member" }
                """));
    }

    @Test
    void aRowThatNamesOnlyACaseAgreesWithAFakeBuildingThatCase() {
        assertFalse(anyDisagreement(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found

                fake findMember
                    | (MemberId("m-1")) -> Found { id = MemberId("m-9") }
                """),
                "the row asserts the case and nothing under it");
    }

    @Test
    void twoValuesOfOneCaseThatDifferInAFieldDisagree() {
        assertTrue(anyDisagreement(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | (MemberId("m-1")) -> Found { id = MemberId("m-9") }
                """));
    }

    // --- a `with` --------------------------------------------------------------------------------

    private static final String CLOCKED = """
            module example.clocked

            data Stamp = { at: String }
            data Note = { at: String }

            behavior now : () -> Stamp

            behavior record : (text: String) -> Note
                depends on now
                constructs Note

            let record (text, now) = Note { at = now().at }

            example now
                | "the clock reads noon" : () -> Stamp { at = "12:00" }
            """;

    @Test
    void aWithOnADependencyThatTakesNoInputIsHeldAgainstItsRecordedRow() {
        assertTrue(anyDisagreement(CLOCKED + """

                example record
                    | "stamped" : ("x") with now = Stamp { at = "09:00" } -> Note { at = "09:00" }
                """));
    }

    @Test
    void aWithThatAgreesWithTheRecordedRowSaysNothing() {
        assertFalse(anyDisagreement(CLOCKED + """

                example record
                    | "stamped" : ("x") with now = Stamp { at = "12:00" } -> Note { at = "12:00" }
                """));
    }

    /**
     * A `with` on a dependency that takes inputs says nothing about which of them it answers: what
     * reaches the dependency is whatever the parent behavior computes and passes. Rows faking two
     * answers for two orders are each right about their own, and holding either against every
     * recorded row would report a model that agrees with itself as contradicting.
     */
    @Test
    void rowLocalWithsForAnInputTakingDependencyDoNotDisagreeWithItsRecordedRows() {
        assertFalse(anyDisagreement(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }
                    | "m-2 is not"      : (MemberId("m-2")) -> Missing { why = "no such member" }

                example place
                    | "m-1 may order" : (Order { by = MemberId("m-1") })
                        with findMember = Found { id = MemberId("m-1") }
                        -> Placed { by = MemberId("m-1") }
                    | "m-2 is refused" : (Order { by = MemberId("m-2") })
                        with findMember = Missing { why = "no such member" }
                        -> Refused { why = "unknown" }
                """));
    }

    @Test
    void aWithOnADependencyThatTakesInputsIsNotComparedAtAll() {
        assertFalse(anyDisagreement(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                example place
                    | "refused" : (Order { by = MemberId("m-1") })
                        with findMember = Missing { why = "no such member" } -> Refused { why = "unknown" }
                """));
    }

    @Test
    void aWithDoesNotSettleWhatTheTableStates() {
        // The `with` takes precedence while this row runs. That is dispatch: the table is still a
        // statement about the same behavior, written for every other row and every other run.
        List<Located> found = disagreements(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | _ -> Missing { why = "no such member" }

                example place
                    | "placed" : (Order { by = MemberId("m-1") })
                        with findMember = Found { id = MemberId("m-1") } -> Placed { by = MemberId("m-1") }
                """);

        // The table disagrees, and is said at both of its ends. The `with` beside it is not compared
        // and does not stop the table from being.
        assertEquals(2, found.size(), found.toString());
    }

    // --- across files ----------------------------------------------------------------------------

    @Test
    void aFakeInTheModuleIsHeldAgainstARowInAnAttachedFile() {
        String module = BASE + """

                fake findMember
                    | (MemberId("m-1")) -> Missing { why = "no such member" }
                """;
        String attached = """
                examples for example.clash

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }
                """;

        assertSaidInBothFiles(module, attached,
                "each statement is said in the file it is written in");
    }

    @Test
    void aFakeInAnAttachedFileIsHeldAgainstARowInTheModule() {
        String module = BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }
                """;
        String attached = """
                examples for example.clash

                fake findMember
                    | (MemberId("m-1")) -> Missing { why = "no such member" }
                """;

        assertSaidInBothFiles(module, attached,
                "the attached file wrote only the fake, and still says its side");
    }

    /** One disagreement across two sources: two diagnostics, one quoting each file. */
    private static void assertSaidInBothFiles(String module, String attached, String why) {
        List<Located> out = new ArrayList<>();
        assertDoesNotThrow(() -> Compiler.compiledModules(
                List.of(module, attached), ModulePath.EMPTY, out));
        List<Located> found = onlyDisagreements(out);

        assertEquals(2, found.size(), found.toString());
        List<Integer> sources = new ArrayList<>();
        for (Located w : found) {
            sources.add(w.sourceIndex());
        }
        assertTrue(sources.contains(0) && sources.contains(1), why + ": " + sources);
    }

    // --- what is not said ------------------------------------------------------------------------

    @Test
    void aRowWhoseInputWillNotBuildIsNotHeldAgainstAnything() {
        // The input breaks its type's invariant, which is E1903's to say. Nothing was read off the
        // row, so there is no answer of its to disagree with.
        List<String> codes = new ArrayList<>();
        CompileException e = org.junit.jupiter.api.Assertions.assertThrows(CompileException.class,
                () -> Compiler.compile("""
                        module example.clash
                        import String ( length )

                        data MemberId = String
                            invariant length(value) > 0

                        data Found = { id: MemberId }
                        data Missing = { why: String }

                        behavior findMember : (id: MemberId) -> Found | Missing

                        example findMember
                            | "empty" : (MemberId("")) -> Found { id = MemberId("m-1") }

                        fake findMember
                            | (MemberId("m-1")) -> Missing { why = "no such member" }
                        """));
        for (souther.compiler.diag.Diagnostic d : e.diagnostics()) {
            codes.add(d.code());
        }
        assertTrue(codes.contains("E1903"), codes.toString());
        assertFalse(codes.contains("E1919"), codes.toString());
    }

    /**
     * A measured compile evaluates every row a second time, against instrumented classes
     * ({@code Adequacy.ProbedExamples}). The disagreement is read off the text and not off either
     * run, so what is said does not depend on how many times the rows were run.
     */
    @Test
    void aDisagreementIsSaidOnceWhateverIsBeingMeasured() {
        String model = BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | (MemberId("m-1")) -> Missing { why = "no such member" }
                """;

        assertEquals(2, measured(model, souther.compiler.query.Adequacy.Asked.NOTHING));
        assertEquals(2, measured(model,
                souther.compiler.query.Adequacy.Asked.reportOnly(
                        souther.compiler.query.Adequacy.Level.ALL)));
    }

    private static int measured(String model, souther.compiler.query.Adequacy.Asked asked) {
        souther.compiler.query.Compilation compilation =
                souther.compiler.query.Compilation.ofSource(model, "Main");
        compilation.measure(asked);
        compilation.answerEverything();
        int said = 0;
        for (souther.compiler.query.Db.Found found : compilation.db().allReports()) {
            if ("E1919".equals(found.report().diagnostic().code())) {
                said++;
            }
        }
        return said;
    }

    @Test
    void theDisagreementReachesTheExamplesReport() throws Exception {
        java.nio.file.Path file = java.nio.file.Files
                .createTempDirectory("souther-disagree").resolve("clash.sou");
        java.nio.file.Files.writeString(file, BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | (MemberId("m-1")) -> Missing { why = "no such member" }
                """);

        java.io.ByteArrayOutputStream err = new java.io.ByteArrayOutputStream();
        java.io.PrintStream was = System.err;
        System.setErr(new java.io.PrintStream(err, true, java.nio.charset.StandardCharsets.UTF_8));
        try {
            Main.main(new String[] {"examples", "--lang", "en", file.toString()});
        } finally {
            System.setErr(was);
        }
        String reported = err.toString(java.nio.charset.StandardCharsets.UTF_8);

        assertTrue(reported.contains("E1919"), reported);
        assertTrue(reported.contains("clash.sou:"), reported);
    }

    @Test
    void theBuildIsNotFailedByADisagreement() {
        assertDoesNotThrow(() -> Compiler.compile(BASE + """

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | (MemberId("m-1")) -> Missing { why = "no such member" }
                """));
    }
}
