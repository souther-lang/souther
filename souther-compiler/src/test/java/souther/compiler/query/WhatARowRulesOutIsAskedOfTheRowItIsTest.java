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
 * Whether an offered row rules a line of a border's family out is asked of the row as it was read
 * back, by the account of offered rows, and nowhere else.
 *
 * <p>The measurement folds the rows in the file through the same range the question is made of
 * ({@code Stands.Ends}, private to the answer), which is what leaves a line standing. An offered row
 * is put to {@link AnotherLineTheRowsAllow.Stands#ruledOutBy} once it is read back, which is what
 * settles an obligation and what lets one row stand for several. Asked anywhere else — of the values
 * a search asked for, before the row they built was read — it is a second account of what a row
 * settles, made from something that is not the row: a search would be skipped on the strength of a
 * row nobody read, and the line it was for would go unlooked at.
 */
class WhatARowRulesOutIsAskedOfTheRowItIsTest {

    private static final Pattern RULES_OUT = Pattern.compile("\\.ruledOutBy\\(");

    @Test
    void onlyTheAccountOfOfferedRowsAsksIt() throws IOException {
        assertEquals(List.of("query/Settlements.java"), callersOf(RULES_OUT));
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
