package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.RowsOfABlock;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.Output;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A string held equal to what a case conversion makes of a string is read through the
 * conversion: a string of the first side is the other's where some string of the other converts
 * to it, which is a statement about the two languages and not about the strings at one place.
 * Where every string the stored side admits is some string's lowercase, the stored side is all
 * reached and no class parts it; where it admits an uppercase letter, the strings that have one
 * are never the lowercase of a string, and the stored side is parted.
 */
class AStoredStringEqualToTheLowercaseOfAStringIsReadTest {

    private static final String DECLARATIONS = """
            module demo

            data Domain = String
                invariant String.matches("PATTERN", value)

            behavior f : (own: Domain, s: String) -> Bool
            let f (own, s) = BODY
            """;

    private static String report(String pattern, String body) {
        Compilation compilation = ACompiledModel.measured(
                DECLARATIONS.replace("PATTERN", pattern).replace("BODY", body),
                Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    private static final List<String> BODIES = List.of("own.value == String.lowercase(s)",
            "String.lowercase(s) == own.value", "own.value /= String.lowercase(s)",
            "String.lowercase(s) /= own.value");

    @Test
    void aStoredStringOfLowercaseLettersIsReachedByTheLowercaseOfAString() {
        for (String body : BODIES) {
            String json = report("[a-z0-9.]+", body);
            assertTrue(json.contains("relation_shown_over_a_region"), () -> body + " " + json);
            assertFalse(json.contains("relation_not_shown_to_reach_every_value"),
                    () -> body + " " + json);
            assertFalse(json.contains("is never String.lowercase(s)"), () -> body + " " + json);
        }
    }

    /** An order between the two is no equality of what the conversion makes, and is not read as
     *  one. */
    @Test
    void anOrderAgainstTheLowercaseIsNotReadThroughTheConversion() {
        for (String body : List.of("own.value < String.lowercase(s)",
                "String.lowercase(s) <= own.value")) {
            String json = report("[a-z0-9.]+", body);
            assertTrue(json.contains("relation_not_shown_to_reach_every_value"),
                    () -> body + " " + json);
            assertFalse(json.contains("relation_shown_over_a_region"), () -> body + " " + json);
        }
    }

    /**
     * A string against its own lowercase is made of one position, which no two texts are: the
     * string is the same in both, so no class says some string of one is the other's.
     */
    @Test
    void aStringAgainstItsOwnLowercaseIsPartedByNothing() {
        for (String source : List.of("""
                module w1
                data P = { s: String, n: Int }
                behavior m : (p: P) -> Bool
                let m (p) = p.s == String.lowercase(p.s)
                """, """
                module w1
                data P = { s: String, n: Int }
                behavior m : (p: P) -> Bool
                let m (p) = String.lowercase(p.s) /= p.s
                """)) {
            Compilation compilation = ACompiledModel.measured(source, Adequacy.Asked.fullReport());
            String json = AdequacyReport.of(compilation)
                    .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
            assertFalse(json.contains("x can be"), () -> source + json);
            assertFalse(json.contains("x is never"), () -> source + json);
        }
    }

    /** A string against its own lowercase is made of one position, which no two texts are. */
    @Test
    void aStringAgainstItsOwnLowercaseIsNotReadAsTwoTexts() {
        String json = report("[a-z0-9.]+", "own.value == String.lowercase(own.value)");
        assertFalse(json.contains("relation_shown_over_a_region"), json);
        assertFalse(json.contains("can be String.lowercase"), json);
    }

    /**
     * The other side is called what it is, the lowercase of {@code s}: a stored string that
     * matches it need not be {@code s}, and no string of {@code s} is the stored one.
     */
    @Test
    void theOtherSideIsNamedByWhatItIsMadeOf() {
        for (String body : BODIES) {
            String json = report("[A-Za-z0-9.]+", body);
            assertTrue(json.contains("own: x can be String.lowercase(s)")
                    && json.contains("own: x is never String.lowercase(s)"),
                    () -> body + " " + json);
            assertFalse(json.contains("own: x can be s\"") || json.contains("own: x is never s\""),
                    () -> body + " " + json);
        }
    }

    /**
     * A string whose lowercase is no string of its own code points is not shown to be a lowercase
     * of anything: the stored side that admits one is not all reached, and the conversion is named
     * as an image not shown.
     */
    @Test
    void aStoredStringThatNoMapOfCodePointsReachesIsNotShownReached() {
        for (String pattern : List.of("[a-zİ]+", "[a-zΣ]+", "[a-zẞ]+")) {
            String json = report(pattern, "own.value == String.lowercase(s)");
            assertTrue(json.contains("\"imagesNotShown\" : [ \"String.lowercase\" ]"),
                    () -> pattern + " " + json);
            assertTrue(json.contains("own: x is never String.lowercase(s)"),
                    () -> pattern + " " + json);
        }
    }

    private static final String ANSWERING = """
            module demo

            data Domain = String
                invariant String.matches("PATTERN", value)
            data Same = { n: Int }
            data Differ = { n: Int }

            behavior f : (own: Domain, s: String) -> Same | Differ
                constructs Same, Differ
            let f (own, s) =
                if BODY then Same { n = 0 } else Differ { n = 0 }
            """;

    /**
     * The rows offered for the classes of {@code s} are run, and between them the comparison comes
     * out both ways: a class is offered a row that stands on each side of the line, whether the
     * stored side is all reached or parted.
     */
    @Test
    void theRowsOfferedForTheClassesReachBothSidesOfTheComparison() {
        for (String pattern : List.of("[a-z0-9.]+", "[A-Za-z0-9.]+")) {
            for (String body : BODIES) {
                String model = ANSWERING.replace("PATTERN", pattern).replace("BODY", body);
                Compilation offering = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
                String block = GeneratedRows.of(
                        Adequacy.offeredFor(offering.db(), OfferingRequest.overTheModule("demo")),
                        Map.of(), SourceRendering.namedByIdentity(offering.texts()),
                        offering.db()).textInEnglish();
                List<RowsOfABlock.Row> offered = RowsOfABlock.of(block);
                assertFalse(offered.isEmpty(), () -> pattern + " " + body + " " + block);

                String examples = offered.stream()
                        .map(row -> "    | " + row.values().replace("<?>", "Same"))
                        .collect(Collectors.joining("\n"));
                // Every row is written as answering Same, so each that answers Differ is refused
                // for not holding, and that is the only thing the model is refused for.
                Compilation running = Compilation.ofSource(
                        model + "\nexample f\n" + examples + "\n", "Main");
                running.answerEverything();
                assertEquals(Set.of("E1905"), running.errors().stream()
                        .map(e -> e.diagnostic().code()).collect(Collectors.toSet()));
                Output.Examples key = Output.Examples.asked(running.db(), "demo",
                        running.sourceIds().get(0));
                Set<String> answered = running.db().ask(key).value().rows().stream()
                        .map(row -> row.resultArm().name()).collect(Collectors.toSet());
                assertEquals(Set.of("Same", "Differ"), answered,
                        () -> pattern + " " + body + "\n" + examples);
            }
        }
    }

    @Test
    void aStoredStringThatMayHaveUppercaseLettersIsPartedFromTheOnesNoLowercaseIs() {
        for (String body : BODIES) {
            String json = report("[A-Za-z0-9.]+", body);
            assertFalse(json.contains("relation_not_shown_to_reach_every_value"),
                    () -> body + " " + json);
            assertTrue(json.contains("own: x can be String.lowercase(s)")
                    && json.contains("own: x is never String.lowercase(s)"),
                    () -> body + " " + json);
        }
    }
}
