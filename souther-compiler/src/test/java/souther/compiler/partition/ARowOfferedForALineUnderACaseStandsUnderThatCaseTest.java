package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row offered for a line under a case is a row at that case.
 *
 * <p>What a line is written about and what a row offered for it has to be are one statement
 * (ADR-0114): a boundary at {@code query.tag@Tag} is a line about the values a {@code Tag} standing
 * at {@code tag} takes, and a row whose {@code tag} is a {@code NoTag} stands nowhere near it. The
 * requirement saying so is written in the path the line is at and is read from there and nowhere
 * else, so a caller composing a row for the line has it already.
 *
 * <p><b>Written as two orders of one sum, because the order is what made the defect visible rather
 * than what caused it.</b> The requirement was dropped either way; where the case carrying a value
 * is declared first, the search happened to reach that case's values before the unit case's and the
 * row came out right. So a test written on one order alone passes over a generator that reads no
 * requirement at all — which is what it did — and the two together say the answer does not depend
 * on the order a sum's cases were written in.
 */
class ARowOfferedForALineUnderACaseStandsUnderThatCaseTest {

    /** A `Tag` behind a case of a sum, with the length invariant that draws the line. */
    private static String filteredBy(String cases) {
        return """
                module example.filter

                data Tag = String
                    invariant String.length(value) >= 1

                data NoTag
                data Filter = %s

                data Query = { tag: Filter, other: Tag }
                data Page = { count: Int }

                behavior readArticles : (query: Query) -> Page

                example readArticles
                    | "no filter" : (Query { tag = NoTag, other = Tag("x") }) -> Page { count = 0 }
                    | "a tag"     : (Query { tag = Tag("dragons"), other = Tag("x") }) -> Page { count = 1 }
                """.formatted(cases);
    }

    @Test
    void aRowForTheLineUnderTheCaseCarriesThatCase() {
        for (String cases : List.of("Tag | NoTag", "NoTag | Tag")) {
            List<String> offered = offeredFor("String.length(query.tag@Tag) = 1",
                    filteredBy(cases));
            assertTrue(!offered.isEmpty(),
                    "a row is offered for the line under `Tag` where `Filter` is `" + cases + "`");
            for (String row : offered) {
                assertTrue(row.contains("tag = Tag("),
                        "a row offered for a line under `Tag` puts a `Tag` there, and `" + cases
                                + "` offered: " + row);
            }
        }
    }

    /** The rows the generator composed for the point labelled {@code point}, as they are written. */
    private static List<String> offeredFor(String point, String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, Adequacy.Filling> all =
                Adequacy.generatedOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, "the model under test compiles");
        return all.get("readArticles").boundaries().rows().stream()
                .filter(row -> row.purposes().stream().anyMatch(p -> p.toString().contains(point)))
                .map(row -> String.join(", ", row.inputs().stream().map(i -> i.text()).toList()))
                .toList();
    }
}
