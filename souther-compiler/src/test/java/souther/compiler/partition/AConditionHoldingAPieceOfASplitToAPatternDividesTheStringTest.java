package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;
import souther.runtime.Strings;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Some piece of a string split at a separator being in a language is a statement about the
 * string, and divides the position the string stands at into the strings that hold such a piece
 * and those that hold none.
 *
 * <p>Held against the runtime: the two rows the model is offered are one for each side of what the
 * condition comes to for the string, as the runtime's own {@code split} and a pattern say, and a
 * row on one side is never taken for a row on the other.
 */
class AConditionHoldingAPieceOfASplitToAPatternDividesTheStringTest {

    private static final String PATTERN = "[A-Z]{2}[0-9]";

    private static final String MATCHES = "String.matches(\"" + PATTERN + "\", t)";

    private static final String SPLIT = "String.split(\";\", list.value)";

    /** A condition over the pieces, and what it comes to for a string. */
    private record Condition(String written, Predicate<List<String>> ofThePieces) {}

    private static boolean matches(String piece) {
        return Pattern.matches(PATTERN, piece);
    }

    private static Map<String, Condition> conditions() {
        Map<String, Condition> out = new LinkedHashMap<>();
        out.put("some", new Condition("List.any(t -> " + MATCHES + ", " + SPLIT + ")",
                pieces -> pieces.stream().anyMatch(AConditionHoldingAPieceOfASplitToAPatternDividesTheStringTest::matches)));
        out.put("every", new Condition("List.all(t -> " + MATCHES + ", " + SPLIT + ")",
                pieces -> pieces.stream().allMatch(AConditionHoldingAPieceOfASplitToAPatternDividesTheStringTest::matches)));
        out.put("some that does not", new Condition(
                "List.any(t -> Bool.not(" + MATCHES + "), " + SPLIT + ")",
                pieces -> pieces.stream().anyMatch(each -> !matches(each))));
        out.put("every that does not", new Condition(
                "List.all(t -> Bool.not(" + MATCHES + "), " + SPLIT + ")",
                pieces -> pieces.stream().noneMatch(AConditionHoldingAPieceOfASplitToAPatternDividesTheStringTest::matches)));
        out.put("some past the first", new Condition(
                "List.any(t -> " + MATCHES + ", List.drop(1, " + SPLIT + "))",
                pieces -> pieces.stream().skip(1).anyMatch(AConditionHoldingAPieceOfASplitToAPatternDividesTheStringTest::matches)));
        out.put("some of the two past the first", new Condition(
                "List.any(t -> " + MATCHES + ", List.take(2, List.drop(1, " + SPLIT + ")))",
                pieces -> pieces.stream().skip(1).limit(2).anyMatch(AConditionHoldingAPieceOfASplitToAPatternDividesTheStringTest::matches)));
        out.put("some of the first two past the first", new Condition(
                "List.any(t -> " + MATCHES + ", List.drop(1, List.take(2, " + SPLIT + ")))",
                pieces -> pieces.stream().limit(2).skip(1).anyMatch(AConditionHoldingAPieceOfASplitToAPatternDividesTheStringTest::matches)));
        return out;
    }

    private static String model(String condition, String declarations) {
        return """
                module example.codes

                data Codes = String
                %s

                behavior hasCode : (list: Codes) -> Bool
                let hasCode (list) = if %s then true else false
                """.formatted(declarations, condition);
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return compilation;
    }

    private static final Pattern A_ROW_VALUE = Pattern.compile("Codes\\(\"([^\"]*)\"\\)");

    private static List<String> offeredFor(Compilation compilation) {
        String offered = GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("example.codes")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
        List<String> values = new ArrayList<>();
        Matcher found = A_ROW_VALUE.matcher(offered);
        while (found.find()) {
            values.add(found.group(1));
        }
        return values;
    }

    /**
     * Two rows are offered, and the condition comes out true for one and false for the other, as
     * the runtime parts the string into pieces and as a pattern accepts them: a row for the strings
     * with such a piece and one for those with none, and never two of the same side.
     */
    @Test
    void theRowsOfferedStandOnTheTwoSidesOfWhatTheConditionComesTo() {
        conditions().forEach((name, condition) -> {
            List<String> rows = offeredFor(measured(model(condition.written(), "")));
            assertEquals(2, rows.size(), () -> name + ": " + rows);
            assertNotEquals(
                    condition.ofThePieces().test(Strings.split(rows.get(0), ";")),
                    condition.ofThePieces().test(Strings.split(rows.get(1), ";")),
                    () -> name + ": two rows of one side: " + rows);
        });
    }

    private static String report(String written, String rows) {
        Compilation compilation = measured(model(written, "") + rows);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** A row on each side of the condition meets both classes, and nothing is left owed. */
    @Test
    void aRowOnEachSideMeetsBothClasses() {
        String report = report(conditions().get("some").written(), """

                example hasCode
                    | "one" : (Codes("AB7")) -> true
                    | "none" : (Codes("")) -> false
                """);
        assertTrue(report.contains("equivalence partitions 2/2"), report);
        assertTrue(report.contains("adequacy: satisfied"), report);
    }

    /**
     * A row on one side leaves the other owed. Held for both ways round, so that neither class is
     * taken as met by the row of the other.
     */
    @Test
    void aRowOnOneSideLeavesTheOtherClassOwed() {
        for (String only : List.of("""

                example hasCode
                    | "one" : (Codes("AB7")) -> true
                """, """

                example hasCode
                    | "none" : (Codes("")) -> false
                """)) {
            String report = report(conditions().get("some").written(), only);
            assertTrue(report.contains("equivalence partitions 1/2"), report);
            assertTrue(!report.contains("adequacy: satisfied"), report);
        }
    }

    /**
     * What the type leaves of the position is met with: a string that has to be shorter than any
     * piece of the language leaves no string with such a piece, so the position is not divided and
     * no row is offered for a side no string of the type is on.
     */
    @Test
    void aSideTheTypeLeavesNoStringOnIsNoClass() {
        String declarations = """
                    invariant String.length(value) <= 2
                """;
        List<String> rows = offeredFor(measured(
                model(conditions().get("some").written(), declarations)));
        for (String row : rows) {
            assertTrue(!matches(row) && row.length() <= 2,
                    () -> "a row of the type that is on the side no string is on: " + rows);
        }
    }
}
