package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A narrowing may stand where another left the position, and what is built there is what both of
 * them left.
 *
 * <p>A refinement does not move to another position and takes no level (ADR-0114), so two of them
 * can stand at one: an optional holding a sum is narrowed to what it holds and then to the case that
 * turned out to be there, and {@code query.tag@Some@Tag} is one position with two narrowings at it.
 * {@code TermPath.requirements} writes both, each against the position it was taken at.
 *
 * <p>The plan read one and went on to the shape, so it built the sum and chose whatever the sum's
 * candidates offered first — which is the defect at {@code query.tag@Tag} (#1070) reappearing one
 * narrowing deeper, and reached by a model that writes `Filter?` rather than by anything unusual.
 * Held end to end, because a plan that stops early and a row that stands at the point are the two
 * ends of the same statement.
 */
class ANarrowingMayStandWhereAnotherLeftThePositionTest {

    /** An optional holding a sum, one of whose cases carries the rules. */
    private static final String OPTIONAL_OF_SUM = """
            module example.chain

            data Tag = String
                invariant String.length(value) >= 1

            data NoTag
            data Filter = NoTag | Tag

            data Query = { tag: Filter? }
            data Page = { count: Int }

            behavior look : (query: Query) -> Page

            example look
                | "none" : (Query { }) -> Page { count = 0 }
            """;

    /**
     * The line the case's own type draws is owed under both narrowings, and the row offered for it
     * carries the case.
     *
     * <p>{@code NoTag} is written first on purpose. The narrowing being dropped is invisible where
     * the case carrying a value is the first the search reaches, so a model that hid it would pass
     * over the plan reading no narrowing at all.
     */
    @Test
    void aRowForALineTwoNarrowingsDeepCarriesBoth() {
        List<String> offered =
                offeredFor("String.length(query.tag@Some@Tag) = 1", OPTIONAL_OF_SUM);

        assertFalse(offered.isEmpty(), "a row is offered for the line under `Some` and then `Tag`");
        for (String row : offered) {
            assertTrue(row.contains("tag = Tag("),
                    "a row for a line under `Some@Tag` puts a `Tag` there: " + row);
            assertFalse(row.contains("tag = NoTag"),
                    "the second narrowing is not the first one read twice: " + row);
            assertFalse(row.contains("tag = None"),
                    "nor is the first one dropped: " + row);
        }
    }

    /** And a narrowing under a field of a case still works, which is one at each of two positions
     *  rather than two at one. */
    private static final String OPTIONAL_UNDER_A_CASE = """
            module example.undercase

            data Tag = String
                invariant String.length(value) >= 1

            data Rejected = { why: Int }
            data Approved = { note: Tag? }
            data Decision = Approved | Rejected
            data Page = { count: Int }

            behavior look : (d: Decision) -> Page

            example look
                | "no" : (Rejected { why = 1 }) -> Page { count = 0 }
            """;

    @Test
    void aNarrowingUnderAFieldOfACaseIsUnaffected() {
        List<String> offered =
                offeredFor("String.length(d@Approved.note@Some) = 1", OPTIONAL_UNDER_A_CASE);

        assertFalse(offered.isEmpty(), "a row is offered for the line under the case's own field");
        for (String row : offered) {
            assertTrue(row.contains("note = Tag("),
                    "and it puts a value at the field the line is under: " + row);
        }
    }

    private static List<String> offeredFor(String point, String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertNotNull(Adequacy.generatedOf(compilation.db(), compilation.modules().get(0)),
                "the model under test compiles");
        // Both of what a person is offered at this behavior's lines. A line an `invariant` drew is
        // the declaration's and is resolved once for the module (issue #1076); a line this body
        // drew is its own.
        return souther.compiler.OfferedAtTheLines.of(compilation,
                        compilation.modules().get(0), "look").rows().stream()
                .filter(row -> row.purposes().stream().anyMatch(p -> p.toString().contains(point)))
                .map(row -> String.join(", ", row.inputs().stream().map(i -> i.text()).toList()))
                .toList();
    }
}
