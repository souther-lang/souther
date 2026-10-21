package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.GeneratedRows;

import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The rows the compiler composes for exactly three of six written values: the count is read as a
 * count, and the rows it composes are rows of the count — some with two of the values above
 * nought, some with three and some with four, which are the rows on each side of the boundary.
 *
 * <p>Through the whole pipeline, from the source to the rows offered. What it guards is that a
 * count reaches the end of it and is composed against; which line decides where, and which ways
 * a count is judged along, are asked of the layers that decide them
 * ({@code WhereALineOfACountDecidesWhereTheOthersComeToTheNumbersAroundItTest} and
 * {@code ACountOfStatementsIsJudgedAsACountTest}), since the combinations of the decisions
 * compose rows with every number above nought whichever way those come out.
 */
class RowsComposedForACountOfWrittenValuesStandOnBothSidesOfItsBoundaryTest {

    private static final Pattern FIELD = Pattern.compile("f\\d = (\\d+)");

    private static final Pattern ROW = Pattern.compile("^\\s*\\| (?:\"[^\"]*\" : )?\\(W \\{.*$",
            Pattern.MULTILINE);

    private static String model(int n, int k) {
        String fields = IntStream.range(0, n).mapToObj(at -> "f" + at + ": Int")
                .collect(Collectors.joining(", "));
        String values = IntStream.range(0, n).mapToObj(at -> "w.f" + at)
                .collect(Collectors.joining(", ", "[", "]"));
        String ones = IntStream.range(0, n).mapToObj(at -> "f" + at + " = " + (at < k ? 1 : 0))
                .collect(Collectors.joining(", "));
        return """
                module p
                import List ( filter, length )
                data W = { %s }
                behavior f : (w: W) -> Int
                let f (w) = if length(filter(x -> x > 0, %s)) == %d then 1 else 2
                example f
                    | "a" : (W { %s }) -> 1
                """.formatted(fields, values, k, ones);
    }

    /** How many values above nought each composed row holds. */
    private static Set<Integer> aboveNoughtInEachRow(String block) {
        Set<Integer> out = new TreeSet<>();
        Matcher rows = ROW.matcher(block);
        while (rows.find()) {
            Matcher fields = FIELD.matcher(rows.group());
            int above = 0;
            while (fields.find()) {
                above += Integer.parseInt(fields.group(1)) > 0 ? 1 : 0;
            }
            out.add(above);
        }
        return out;
    }

    @Test
    void rowsAreComposedWithOneFewerTheNumberAndOneMoreAboveNought() {
        Compilation compilation = Compilation.ofSource(model(6, 3), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        String block = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("p")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();

        Set<Integer> above = aboveNoughtInEachRow(block);
        assertTrue(above.containsAll(Set.of(2, 3, 4)),
                () -> "rows on both sides of the boundary, got " + above + " in " + block);
    }
}
