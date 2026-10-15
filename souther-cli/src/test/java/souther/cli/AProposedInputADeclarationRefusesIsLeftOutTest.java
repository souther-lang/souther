package souther.cli;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An input a declaration refuses is not named for a line the rows leave standing, and the line is
 * still said to stand.
 *
 * <p>Two things are asked and they are independent. Which line the rows leave standing is read off
 * the rows and the model, and is the same whatever the positions' types are; where a row could be
 * written to tell the two lines apart is a further answer, and one a declaration can take away. A
 * sentence that lost its line with the input would say the rows tell the lines apart, which they do
 * not.
 */
class AProposedInputADeclarationRefusesIsLeftOutTest {

    private static final String ROWS = """
              | (Amount(0.0m), Amount(0.0m))   -> true
              | (Amount(0.0m), Amount(1.0m))   -> false
              | (Amount(13.0m), Amount(23.0m)) -> true
              | (Amount(12.0m), Amount(24.0m)) -> true""";

    private static String over(String typeOfAPosition, String rows) {
        return """
                module m

                data Amount = Decimal
                    invariant value >= 0.0m

                behavior f : (x: %s, y: %s) -> Bool

                let f (x, y) = {
                    guard y %s <= 2.0m * x %s else false

                    true
                }

                example f
                %s
                """.formatted(typeOfAPosition, typeOfAPosition,
                typeOfAPosition.equals("Amount") ? ".value" : "",
                typeOfAPosition.equals("Amount") ? ".value" : "", rows);
    }

    @Test
    void theLineStaysAndTheInputADeclarationRefusesGoes() {
        List<String> declared = findings(run(over("Amount", ROWS)));
        List<String> undeclared = findings(run(over("Decimal", ROWS.replace("Amount(", "("))));

        assertEquals(1, undeclared.size(), () -> "the plain positions leave a line standing: "
                + undeclared);
        assertEquals(1, declared.size(), () -> "and the declared ones leave the same line standing: "
                + declared);
        // What the case is about: with nothing refused the input stepping along the line lands on
        // is a negative one, so the declared run has something to leave out.
        assertTrue(undeclared.get(0).contains(", and a row at ")
                        && undeclared.get(0).contains("= -"),
                () -> "the plain positions are named an input below nought: " + undeclared);
        assertFalse(declared.get(0).contains("= -"),
                () -> "an amount that cannot be negative is not named as one: " + declared);
        assertEquals(undeclared.get(0).replaceFirst(", and a row at.*$", ""),
                declared.get(0).replaceFirst(", and a row at.*$", ""),
                "the line the rows leave standing does not depend on where a row could be written");
    }

    private static List<String> findings(String report) {
        List<String> said = new ArrayList<>();
        for (String line : report.split("\n")) {
            if (line.contains("no row tells")) {
                said.add(line.strip().replaceFirst("^! ", ""));
            }
        }
        return said;
    }

    private static String run(String source) {
        try {
            Path file = Files.createTempDirectory("souther-refused").resolve("m.sou");
            Files.writeString(file, source);
            PrintStream out = System.out;
            PrintStream err = System.err;
            ByteArrayOutputStream said = new ByteArrayOutputStream();
            System.setOut(new PrintStream(said, true, StandardCharsets.UTF_8));
            System.setErr(new PrintStream(said, true, StandardCharsets.UTF_8));
            try {
                Main.dispatch(new String[] {"examples", "--generate", file.toString()});
            } finally {
                System.setOut(out);
                System.setErr(err);
            }
            return said.toString(StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
}
