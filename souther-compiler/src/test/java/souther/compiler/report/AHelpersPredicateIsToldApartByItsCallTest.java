package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A predicate a helper applies is told apart by the call of the helper wherever the page names a
 * reading of it.
 *
 * <p>The helper applies one predicate, which is one place in the source, and the body calls it with
 * its arguments one way round and then the other. Neither reading states strings this compiler
 * works out, and each is about the argument its own call handed over — so a line about one names
 * that call, and a page naming the place alone shows the two as one rule read twice about two
 * different values.
 */
class AHelpersPredicateIsToldApartByItsCallTest {

    private static final String MODEL = """
            module example.prefixes

            behavior k : (a: String, b: String) -> Int

            let has (c: String, p: String): Bool = String.startsWith(c, p)

            let k (a, b) = if has(a, b) then 1 else (if has(b, a) then 2 else 3)
            """;

    @Test
    void aReadingOfTheHelpersPredicateNamesTheCallItWasReadAt() {
        List<String> lines = page().lines().filter(line -> line.contains("· not read: predicate@"))
                .toList();
        assertFalse(lines.isEmpty(), "the helper's predicate is read at both calls and worked out"
                + " at neither");
        Set<String> named = new LinkedHashSet<>();
        for (String line : lines) {
            String expected = line.contains("about `b`") ? call("has(a, b)") : call("has(b, a)");
            assertEquals(Set.of(expected), callsIn(line),
                    () -> "the call that handed over the value the reading is about: " + line);
            named.addAll(callsIn(line));
        }
        assertEquals(Set.of(call("has(a, b)"), call("has(b, a)")), named,
                "and each call is named by the reading made at it");
    }

    /** Where the body writes {@code written}, as the page names the call, read off the model's
     *  text. */
    private static String call(String written) {
        List<String> lines = MODEL.lines().toList();
        for (int i = 0; i < lines.size(); i++) {
            int at = lines.get(i).indexOf(written);
            if (at >= 0 && lines.get(i).strip().startsWith("let k")) {
                return "has@" + (i + 1) + ":" + (at + 1);
            }
        }
        throw new AssertionError("the body writes " + written);
    }

    private static Set<String> callsIn(String text) {
        Set<String> out = new LinkedHashSet<>();
        Matcher call = Pattern.compile("has@\\d+:\\d+").matcher(text);
        while (call.find()) {
            out.add(call.group());
        }
        return out;
    }

    private static String page() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
