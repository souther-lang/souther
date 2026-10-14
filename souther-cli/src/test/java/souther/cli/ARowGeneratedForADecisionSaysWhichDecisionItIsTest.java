package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A row generated for a decision rule or a combination of decisions says which one, by the
 * conditions the report says it by — and a row handed for a point of a line says which point.
 *
 * <p>Neither has a name a row could carry: what tells one rule from another is every condition it
 * turns on, and each condition is a place, which would go stale in a row's name. So the row goes
 * unnamed and says over itself which rule and which combination it fills, condition by condition
 * — the words the page writes under `decision` and `interaction`, so that a reader can match the
 * row to the gap.
 */
class ARowGeneratedForADecisionSaysWhichDecisionItIsTest {

    private static final String MODEL = """
            data On
            data Off
            data Flag = On | Off

            behavior both : (a: Flag, b: Flag) -> Int

            let both (a, b) = {
                let x = match a with
                    | On -> 1
                    | Off -> 0
                let y = match b with
                    | On -> 2
                    | Off -> 0
                x + y
            }

            example both
                | (On, On) -> 3
                | (Off, Off) -> 0
            """;

    @Test
    void eachRowSaysTheRuleAndTheCombinationItFillsByTheirConditions() throws Exception {
        String generated = generated();

        assertEquals(List.of(
                        "// fills a combination of the decisions (it goes through `case Off` (8:13);"
                                + " it goes through `case On` (11:13))",
                        "// fills a decision rule (it goes through `case Off` (8:13); it goes"
                                + " through `case On` (11:13))",
                        "// fills a combination of the decisions (it goes through `case On` (8:13);"
                                + " it goes through `case Off` (11:13))",
                        "// fills a decision rule (it goes through `case On` (8:13); it goes"
                                + " through `case Off` (11:13))"),
                generated.lines().filter(line -> line.startsWith("// fills")).toList(),
                generated);
    }

    /**
     * A row handed for a point of a line says which point. It is never composed for one — what a
     * line is owed is answered in the account — so the point is the offering's answer of which row
     * is handed for the line, said over the row in the words the report says the point in.
     */
    @Test
    void aRowHandedForAPointOfALineSaysWhichPoint() throws Exception {
        String generated = generated("rule.sou", """
                behavior both : (a: Int, b: Int) -> Int

                let both (a, b) = {
                    let x = if a > 0 then 1 else 0
                    let y = if b > 0 then 2 else 0
                    x + y
                }

                example both
                    | (1, 1) -> 3
                    | (0, 0) -> 0
                """);

        assertEquals(List.of(
                        "// fills IN point of comparison@rule.sou:4:18",
                        "// fills OUT point of comparison@rule.sou:4:18",
                        "// fills IN point of comparison@rule.sou:5:18",
                        "// fills OUT point of comparison@rule.sou:5:18"),
                generated.lines().filter(line -> line.startsWith("// fills")).toList(),
                generated);
    }

    /** {@code souther examples --generate} over the model, and what it printed. */
    private static String generated() throws Exception {
        return generated("flags.sou", MODEL);
    }

    private static String generated(String name, String source) throws Exception {
        Path file = Files.createTempDirectory("souther-generate").resolve(name);
        Files.writeString(file, source);
        PrintStream originalOut = System.out;
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        System.setOut(new PrintStream(out, true, StandardCharsets.UTF_8));
        try {
            Main.dispatch(new String[] {"examples", "--generate", file.toString()});
        } finally {
            System.setOut(originalOut);
        }
        return out.toString(StandardCharsets.UTF_8);
    }
}
