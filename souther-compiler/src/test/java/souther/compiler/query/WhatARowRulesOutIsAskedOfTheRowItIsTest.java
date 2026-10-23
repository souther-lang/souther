package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a row rules a line of a border's family out is asked of the row as it was read back, in
 * one place, and nowhere else.
 *
 * <p>The measurement folds the rows in the file through the same fold the question is made of
 * ({@code Stands.Fold}), which is what leaves a line standing. A row is put to
 * {@link AnotherLineTheRowsAllow.Stands#ruledOutBy} once it is read back ({@link WhatARowRulesOut}):
 * an offered row, which is what settles an obligation and what lets one row stand for several, and a
 * row a search composed and saw run to the rule, which is what shows an input arriving. Asked
 * anywhere else — of the values a search asked for, before the row they built was read — it is a
 * second account of what a row settles, made from something that is not the row: a search would be
 * skipped on the strength of a row nobody read, and a line named at an input no row holds.
 */
class WhatARowRulesOutIsAskedOfTheRowItIsTest {

    private static final Pattern RULES_OUT = Pattern.compile("\\.ruledOutBy\\(");

    @Test
    void onlyTheReadingOfARowReadBackAsksIt() throws IOException {
        assertEquals(List.of("query/WhatARowRulesOut.java"), callersOf(RULES_OUT));
    }

    /** Every main source that calls it, by its path under the compiler's package. */
    private static List<String> callersOf(Pattern call) throws IOException {
        Path main = Path.of("src/main/java/souther/compiler");
        assertTrue(Files.isDirectory(main), () -> "no " + main.toAbsolutePath());
        List<String> out = new ArrayList<>();
        try (Stream<Path> walk = Files.walk(main)) {
            for (Path source : walk.filter(each -> each.toString().endsWith(".java")).sorted()
                    .toList()) {
                if (call.matcher(Files.readString(source)).find()) {
                    String path = source.toString().replace('\\', '/');
                    out.add(path.substring(path.indexOf("souther/compiler/")
                            + "souther/compiler/".length()));
                }
            }
        }
        return out;
    }
}
