package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Moving a helper into another module does not change what a behavior that calls it is measured
 * against.
 *
 * <p>The examples report reads the tree in which the language's own operations still stand as
 * operations, and a helper is expanded into it whichever module declared the helper. An imported
 * helper arrives already closed by its own module, so that closing has to be done in the same
 * representation the reader expands in. Closed for the backend instead, it brings the body of
 * {@code List.drop} with it, and the comparison inside that body is one no author wrote.
 *
 * <p>The helper's own comparison is the control: it is the author's, and it is owed rows wherever
 * the helper is declared.
 */
class AnImportedHelperIsMeasuredAsItWouldBeBesideTheBehaviorTest {

    private static final String HELPER_BODY = """
            let tailSum (values: List<Int>): Int =
                if List.sum(List.drop(1, values)) > 10 then 10 else List.sum(List.drop(1, values))
            """;

    private static final String BEHAVIOR = """
            behavior calculate : (values: List<Int>) -> Int
            let calculate (values) = tailSum(values)

            example calculate
                | "short" : ([1, 2, 3]) -> 5
            """;

    @Test
    void theImportedFormReportsWhatTheSameModuleFormReports() throws Exception {
        Path dir = Files.createTempDirectory("souther-imported-helper");
        Path same = dir.resolve("same.sou");
        Files.writeString(same, "module repro.same\n\n" + HELPER_BODY + "\n" + BEHAVIOR);
        Path helper = dir.resolve("helper.sou");
        Files.writeString(helper, "module repro.helper exposing ( tailSum )\n\n" + HELPER_BODY);
        Path importer = dir.resolve("imported.sou");
        Files.writeString(importer, "module repro.same\n\nimport repro.helper ( tailSum )\n\n"
                + BEHAVIOR);

        Run beside = examples(same);
        Run across = examples(helper, importer);

        assertEquals(0, beside.code(), () -> "the helper beside the behavior:\n" + beside);
        assertEquals(0, across.code(), () -> "the helper imported:\n" + across);
        assertFalse(across.err().contains("internal compiler error"), across::toString);
        // The helper's own fork is owed a row wherever the helper is declared, so the agreement
        // below is not two reports that both left the helper out.
        assertTrue(across.out().contains("no row goes through `then` (helper.sou:"),
                across::toString);
        assertEquals(measured(beside.out()), measured(across.out()),
                () -> "beside:\n" + beside + "\nimported:\n" + across);
    }

    /** What the report says about {@code calculate}, which is what moving the helper must leave
     * alone. A place in the helper names its file once the helper has one of its own, and that is
     * about where it moved. */
    private static List<String> measured(String report) {
        List<String> out = new ArrayList<>();
        boolean inside = false;
        for (String line : report.split("\n")) {
            if (line.startsWith("  calculate ")) {
                inside = true;
            } else if (inside && !line.startsWith("    ")) {
                break;
            }
            if (inside) {
                out.add(line.replace("helper.sou:", ""));
            }
        }
        return out;
    }

    private record Run(int code, String out, String err) {
        @Override
        public String toString() {
            return "exit " + code + "\n--- out\n" + out + "--- err\n" + err;
        }
    }

    private static Run examples(Path... files) {
        List<String> args = new ArrayList<>(List.of("examples"));
        for (Path file : files) {
            args.add(file.toString());
        }
        PrintStream originalOut = System.out;
        PrintStream originalErr = System.err;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        ByteArrayOutputStream err = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        System.setErr(new PrintStream(err, true, StandardCharsets.UTF_8));
        int code;
        try {
            code = Main.guarded(() -> Main.dispatch(args.toArray(String[]::new)));
        } finally {
            System.setOut(originalOut);
            System.setErr(originalErr);
        }
        return new Run(code, out.toString(StandardCharsets.UTF_8),
                err.toString(StandardCharsets.UTF_8));
    }
}
