package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an optional holds is a position, so what its type says about it is owed and a row is offered
 * for it.
 *
 * <p>Whether an optional holds anything is a narrowing like a sum's case (ADR-0114), so the position
 * under it is {@code tag@Some} and the rules of what it holds are read there. Before that it was
 * nowhere: `Tag?` and `Tag` held the same type, the second was measured against the invariant and
 * the first was reported as rules the walk never reached, and nothing an author could write
 * discharged it — the same boundary was insisted on at one field and owed at neither end of the
 * other (issue #1063).
 *
 * <p><b>Both ends, because each was wrong on its own.</b> The measure has to owe the line, and the
 * generator has to offer a row that stands on it: with the line owed and the requirement dropped on
 * the way to the plan, the row offered for {@code String.length(query.tag@Some) = 1} was
 * {@code tag = None}, which is a row at no point under {@code Some} at all.
 */
class WhatAnOptionalHoldsIsOwedAndOfferedARowTest {

    private static final String TAGGED = """
            module example.tagged

            data Tag = String
                invariant String.length(value) >= 1

            data Query = { tag: Tag?, other: Tag }
            data Page = { count: Int }

            behavior readArticles : (query: Query) -> Page

            example readArticles
                | "no filter" : (Query { other = Tag("x") }) -> Page { count = 0 }
                | "a tag"     : (Query { tag = Tag("dragons"), other = Tag("x") }) -> Page { count = 1 }
            """;

    /** The line the type behind the `?` draws is owed where the optional holds a value. */
    @Test
    void theLineBehindTheQuestionMarkIsOwed() {
        String report = human(TAGGED);

        assertTrue(report.contains("String.length(query.tag@Some) = 1"),
                "the invariant of what the optional holds draws its line at the narrowing: "
                        + report);
        assertTrue(report.contains("String.length(query.other) = 1"),
                "as it does at the field holding the same type outright: " + report);
    }

    /**
     * And the row offered for it holds a value there.
     *
     * <p>Read off what was composed and not off the label it was composed under. What went wrong
     * was exactly a row that carried the label and not the value, so a test that read the label
     * back would have passed over it.
     */
    @Test
    void theRowOfferedForItHoldsAValueThere() {
        List<String> offered = offeredFor("String.length(query.tag@Some) = 1", TAGGED);

        assertFalse(offered.isEmpty(), "a row is offered for the line under `Some`");
        for (String row : offered) {
            assertTrue(row.contains("tag = Tag("),
                    "a row offered for a line under `Some` puts a value there: " + row);
            assertFalse(row.contains("tag = None"),
                    "and a row with nothing at the position stands at no point under it: " + row);
        }
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String human(String source) {
        return AdequacyReport.of(measured(source)).human(SourceNameResolver.identity());
    }

    private static List<String> offeredFor(String point, String source) {
        Compilation compilation = measured(source);
        Map<String, Adequacy.Filling> all =
                Adequacy.generatedOf(compilation.db(), compilation.modules().get(0));
        assertNotNull(all, "the model under test compiles");
        return all.get("readArticles").boundaries().rows().stream()
                .filter(row -> row.purposes().stream().anyMatch(p -> p.toString().contains(point)))
                .map(row -> String.join(", ", row.inputs().stream().map(i -> i.text()).toList()))
                .toList();
    }
}
