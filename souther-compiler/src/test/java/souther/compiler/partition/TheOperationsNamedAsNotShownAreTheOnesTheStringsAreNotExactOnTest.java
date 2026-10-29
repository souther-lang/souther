package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.NavigableSet;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An operation a report names as one whose image is not shown is one a string it is done to is not
 * exactly a map on — and not one that is merely written in the relation.
 *
 * <p>The strings of a side that a conversion is exact on leave nothing open, so a conversion done
 * to them is named for nothing; of two sides, the one the conversion fails on is the one named;
 * and of two conversions done in turn, the one whose step the strings first fail at.
 */
class TheOperationsNamedAsNotShownAreTheOnesTheStringsAreNotExactOnTest {

    private static final Pattern NAMED = Pattern.compile(
            "\"imagesNotShown\"\\s*:\\s*\\[([^\\]]*)\\]");

    private static NavigableSet<String> named(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
        NavigableSet<String> out = new TreeSet<>();
        Matcher found = NAMED.matcher(json);
        while (found.find()) {
            for (String each : found.group(1).split(",")) {
                String name = each.replace("\"", "").trim();
                if (!name.isEmpty()) {
                    out.add(name);
                }
            }
        }
        return out;
    }

    private static String source(String left, String right, String relation) {
        return """
                module demo

                data A = String
                    invariant String.matches("%s", value)

                data B = String
                    invariant String.matches("%s", value)

                behavior f : (a: A, b: B) -> Bool
                let f (a, b) = %s
                """.formatted(left, right, relation);
    }

    /** The first side's lowercase is exact on every string it holds; the second's uppercase is
     *  not, for the one that becomes two code points. */
    @Test
    void ofTwoSidesTheOneTheConversionFailsOnIsNamed() {
        assertEquals(List.of("String.uppercase"), List.copyOf(named(source("[a-z]+", "ß|X",
                "String.contains(String.lowercase(a.value), String.uppercase(b.value))"))));
        assertEquals(List.of("String.lowercase"), List.copyOf(named(source("İ|X", "[A-Z]+",
                "String.contains(String.lowercase(a.value), String.uppercase(b.value))"))));
    }

    @Test
    void aConversionExactOnEveryStringItIsDoneToIsNamedForNothing() {
        assertEquals(List.of(), List.copyOf(named(source("[a-z]+", "[A-Z]+",
                "String.contains(String.lowercase(a.value), String.uppercase(b.value))"))));
    }

    /** Of two done in turn, the uppercase first and the lowercase after, the strings fail at the
     *  uppercase step: the sharp s becomes two, and what the lowercase makes of them is not
     *  where they fail. */
    @Test
    void ofTwoConversionsDoneInTurnTheStepTheStringsFailAtIsNamed() {
        NavigableSet<String> names = named(source("ß|X", "[a-z]+",
                "String.contains(String.lowercase(String.uppercase(a.value)), b.value)"));
        assertTrue(names.contains("String.uppercase"), names::toString);
        assertEquals(List.of("String.uppercase"), List.copyOf(names));
    }
}
