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

    /**
     * A table with a row that will not build is one the fake cannot stand in with at all (E1908), so
     * it answers nothing — not even for the inputs its other rows state. Reading one row of it would
     * report what a fake answers for a table the runner refuses to build.
     */
    @Test
    void aTableWithAnUnbuildableRowAnswersNothing() {
        assertEquals(List.of("E1908"), allCodesOf("""
                module example.clash
                import String ( length )

                data MemberId = String
                    invariant length(value) > 0

                data Found = { id: MemberId }
                data Missing = { why: String }

                behavior findMember : (id: MemberId) -> Found | Missing

                behavior place : (id: MemberId) -> Found | Missing
                    depends on findMember
                let place (id, findMember) = findMember(id)

                example findMember
                    | "m-1 is a member" : (MemberId("m-1")) -> Found { id = MemberId("m-1") }

                fake findMember
                    | (MemberId("m-1")) -> Missing { why = "none" }
                    | (MemberId("m-2")) -> Found { id = MemberId("") }

                example place
                    | "runs" : (MemberId("m-1")) -> Missing { why = "none" }
                """));
    }

    /**
     * A row expecting a case the behavior has no arm for records nothing about it — that is E1904 —
     * so there is no answer of its for a stand-in to disagree with.
     */
    @Test
    void aRowExpectingACaseTheBehaviorCannotAnswerWithStatesNothing() {
        assertEquals(List.of("E1904"), allCodesOf("""
                module example.clash

                data Found = { id: String }
                data Missing = { why: String }
                data Unauthorized = { why: String }

                behavior find : (id: String) -> Found | Missing

                example find
                    | "blocked" : ("m-1") -> Unauthorized { why = "blocked" }

                fake find
                    | ("m-1") -> Missing { why = "none" }
                """));
    }

    /**
     * A row whose fixture will not finish states nothing, so nothing is held against it. What
     * happened is said where the row is evaluated (E1910), and the reading adds nothing beside it.
     *
     * <p>This reaches the reading through {@code builtOrNull}, which drops the row as the fixture
     * failure it is. The other way a reading can end — a helper that overruns the budget on the
     * reading's own worker — is handled where the worker is joined, and nothing here provokes it.
     */
    @Test
    void aRowWhoseFixtureWillNotFinishIsHeldAgainstNothing() {
        CompileException e = org.junit.jupiter.api.Assertions.assertThrows(CompileException.class,
                () -> Compiler.compile("""
                        module example.spin

                        data N = Int
                        data Found = { n: N }
                        data Missing = { why: String }

                        partial let spin (n: Int): Int = spin(n)

                        behavior find : (n: N) -> Found | Missing

                        example find
                            | "loops" : (N(spin(1))) -> Found { n = N(0) }

                        fake find
                            | (N(1)) -> Missing { why = "none" }
                        """));

        List<String> codes = new ArrayList<>();
        for (souther.compiler.diag.Diagnostic d : e.diagnostics()) {
            codes.add(d.code());
        }
        assertTrue(codes.contains("E1910"), codes.toString());
        assertFalse(codes.contains("E1919"), codes.toString());
    }

    /**
     * A `with` stands in with a value or it stands in with nothing. A bare case name is an assertion
     * a row may make and a stand-in may not: `Missing` has fields, so there is no `Missing` to
     * install, and the row is left with nothing to disagree with (E1908 says why).
     */
    @Test
    void aWithThatCannotBeBuiltStandsInForNothing() {
        assertEquals(List.of("E1908"), allCodesOf("""
                module example.b1

                data Found = { id: String }
                data Missing = { why: String }
                data Done

                behavior lookup : () -> Found | Missing

                behavior use : () -> Done
                    depends on lookup
                    constructs Done
                let use (lookup) = match lookup() with
                    | Found   -> Done
                    | Missing -> Done

                example lookup
                    | "found" : () -> Found

                example use
                    | "runs" : () with lookup = Missing -> Done
                """));
    }

    /**
     * A fixture that will not finish costs its own reading and no other. One row read within one
     * budget would let a row nobody is asking about spend what every other statement in the module
     * needed, and a plain contradiction elsewhere would go unsaid because of it.
     */
    @Test
    void aRowThatWillNotFinishDoesNotTakeTheRestOfTheModuleWithIt() {
        assertEquals(List.of("E1910", "E1919", "E1919"), allCodesOf("""
                module example.b2

                data N = Int
                data Found = { id: String }
                data Missing = { why: String }

                partial let spin (n: Int): Int = spin(n)

                behavior findMember : (id: String) -> Found | Missing
                behavior other : (n: N) -> Found | Missing

                example findMember
                    | "clash" : ("m-1") -> Found { id = "m-1" }

                fake findMember
                    | ("m-1") -> Missing { why = "none" }

                example other
                    | "loops" : (N(spin(1))) -> Found { id = "x" }

                fake other
                    | (N(1)) -> Missing { why = "none" }
                """));
    }

    /**
     * Which case a value is comes from the value, not from the call that produced it. A fake row
     * answering through a helper states the case that helper returned, and a row naming only a case
     * is held against that.
     */
    @Test
    void aCaseAHelperAnsweredWithIsWhatTheFakeStates() {
        assertEquals(List.of("E1919", "E1919"), allCodesOf("""
                module example.m3b

                data Found = { id: String }
                data Missing = { why: String }

                let missing (reason: String): Missing = Missing { why = reason }

                behavior lookup : () -> Found | Missing

                example lookup
                    | "found" : () -> Found

                fake lookup
                    | _ -> missing("none")
                """));
    }

    /** The E1919s of a compile that may also fail, read off the reports rather than the warnings —
     * a compile that raises drops the warnings it had collected. */
    private static List<String> codesOf(String model) {
        List<String> codes = new ArrayList<>();
        for (String code : allCodesOf(model)) {
            if ("E1919".equals(code)) {
                codes.add(code);
            }
        }
        return codes;
    }

    /** Every example-family code the compile reported, in order. Read off the reports so that the
     * error a case is really about is visible beside the E1919s, and a test cannot pass by the whole
     * comparison having stopped working. */
    private static List<String> allCodesOf(String model) {
        souther.compiler.query.Compilation compilation =
                souther.compiler.query.Compilation.ofSource(model, "Main");
        compilation.answerEverything();
        List<String> codes = new ArrayList<>();
        for (souther.compiler.query.Db.Found found : compilation.db().allReports()) {
            String code = found.report().diagnostic().code();
            if (code != null && code.startsWith("E19")) {
                codes.add(code);
            }
        }
        return codes;
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
