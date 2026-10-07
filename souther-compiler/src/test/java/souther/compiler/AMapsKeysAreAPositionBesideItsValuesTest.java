package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a map files its values under is read and written at its keys, beside the values and apart
 * from them.
 *
 * <p>A closure over a map is handed the key as well as the value, and a body deciding on the key
 * divides the input there: a class of the key's type, a line drawn on what the key measures, an
 * invariant the key's newtype states. Each is owed, offered and met the whole way round, the way
 * what a list holds is. And the key and the value of one entry go together: a row is read one entry
 * at a time, so a key of one entry and the value of another are not one reading of it.
 */
class AMapsKeysAreAPositionBesideItsValuesTest {

    /** A body keeping the entries filed under one case of an enumeration. */
    private static final String BY_REGION = """
            module example.region

            data Region = North | South

            data Usage = { counts: Map<Region, Int> }

            behavior northern : (u: Usage) -> Map<Region, Int>

            let northern (u) = Map.filterEntries((k, _) -> match k with
                | North -> true
                | South -> false, u.counts)

            example northern
                | "north" : (Usage { counts = [(North, 5)] }) -> [(North, 5)]
            """;

    @Test
    void aCaseOfTheKeyIsOwedOfferedAndThenMet() {
        Compilation before = measured(BY_REGION);
        assertTrue(report(before).contains("no row is in `South` at u.counts[key]"),
                () -> "the case no key was written as is owed at the keys: " + report(before));

        String block = block(before, "example.region");
        assertTrue(block.contains("counts = [(South, 0)]"),
                () -> "a row is offered with a key in that case: " + block);

        Compilation after = measured(BY_REGION + """
                    | "south" : (Usage { counts = [(South, 0)] }) -> []
                """);
        assertEquals(List.of(), gapsOf(after, Adequacy.Kind.AXIS_CLASS_UNCOVERED),
                () -> "the row that was offered meets it: " + report(after));
    }

    /** A body comparing what a key measures against a field beside the map. */
    private static final String LONG_NAMES = """
            module example.names

            data Usage = { counts: Map<String, Int>, atLeast: Int }

            behavior popular : (u: Usage) -> Map<String, Int>

            let popular (u) = Map.filterEntries((k, _) -> String.length(k) >= u.atLeast, u.counts)

            example popular
                | "some" : (Usage { counts = [("abcd", 5), ("b", 1)], atLeast = 3 }) -> [("abcd", 5)]
                | "none" : (Usage { counts = [], atLeast = 3 }) -> []
            """;

    @Test
    void aLineOverWhatAKeyMeasuresIsOwedOfferedAndThenMet() {
        Compilation before = measured(LONG_NAMES);
        assertTrue(report(before).contains("String.length(u.counts[key])"),
                () -> "the rule is read at the keys, and not left as a form nothing reads: "
                        + report(before));
        List<String> unmet = gapsOf(before, Adequacy.Kind.BOUNDARY_UNMET);
        assertFalse(unmet.isEmpty(), () -> "the line is owed rows: " + report(before));

        String block = block(before, "example.names");
        assertTrue(block.contains("counts = [(\"\", 0)], atLeast = 0"),
                () -> "a row is offered on the line, with the key the line is about: " + block);
        assertTrue(block.contains("counts = [(\"\", 0)], atLeast = 1"),
                () -> "and one beside it: " + block);

        Compilation after = measured(LONG_NAMES + """
                    | "on" : (Usage { counts = [("", 0)], atLeast = 0 }) -> [("", 0)]
                    | "off" : (Usage { counts = [("", 0)], atLeast = 1 }) -> []
                """);
        assertEquals(List.of(), gapsOf(after, Adequacy.Kind.BOUNDARY_UNMET),
                () -> "the rows that were offered meet the line: " + report(after));
    }

    /**
     * A body relating each key to the value filed under it, and a row whose entries are on the line
     * only when a key is read beside the other entry's value.
     *
     * <p>{@code "ab"} is filed under 3 and {@code "abc"} under 2: no entry's key is as long as its
     * value, while each key is as long as the value of the other entry.
     */
    private static final String KEY_BESIDE_ITS_VALUE = """
            module example.entries

            data Usage = { counts: Map<String, Int> }

            behavior popular : (u: Usage) -> Map<String, Int>

            let popular (u) = Map.filterEntries((k, v) -> String.length(k) >= v, u.counts)

            example popular
                | "crossed" : (Usage { counts = [("ab", 3), ("abc", 2)] }) -> [("abc", 2)]
            """;

    @Test
    void aKeyIsReadBesideTheValueOfItsOwnEntryAndNoOther() {
        Compilation compilation = measured(KEY_BESIDE_ITS_VALUE);
        String report = report(compilation);
        assertTrue(report.contains("no row is at the ON point"),
                () -> "no entry is on the line, so nothing meets it: " + report);
        assertFalse(report.contains("no row is at the OFF point"),
                () -> "the entry under 3 is one short of it, and meets that point: " + report);
        assertFalse(report.contains("no row is at an IN point"),
                () -> "and the entry under 2 is past it: " + report);
    }

    /** A map keyed by a newtype whose invariant says how long a key is. */
    private static final String CODES = """
            module example.codes

            data Code = String
                invariant longEnough = String.length(value) >= 4

            data Usage = { counts: Map<Code, Int>, atLeast: Int }

            behavior popular : (u: Usage) -> Map<Code, Int>

            let popular (u) = Map.filterEntries((k, _) -> String.length(k.value) >= u.atLeast,
                u.counts)

            example popular
                | "long" : (Usage { counts = [(Code("abcde"), 5)], atLeast = 5 }) -> [(Code("abcde"), 5)]
            """;

    @Test
    void theInvariantOfAKeysNewtypeIsOwedAtTheKeys() {
        Compilation before = measured(CODES);
        String owed = report(before);
        assertTrue(owed.contains("no row is at the ON point String.length(value) = 4"
                        + " (invariant Code (longEnough))"),
                () -> "the newtype's line is owed a row, which a key stands at: " + owed);

        Compilation after = measured(CODES + """
                    | "shortest" : (Usage { counts = [(Code("abcd"), 1)], atLeast = 5 }) -> []
                """);
        String met = report(after);
        assertFalse(met.contains("no row is at the ON point String.length(value) = 4"),
                () -> "and a key written at it meets it: " + met);
    }

    private static List<String> gapsOf(Compilation compilation, Adequacy.Kind kind) {
        return AdequacyReport.of(compilation).adequacyGaps().stream()
                .filter(each -> each.kind() == kind)
                .map(each -> each.about().toString())
                .toList();
    }

    private static String block(Compilation compilation, String module) {
        return GeneratedRows.of(
                Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule(module)),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
