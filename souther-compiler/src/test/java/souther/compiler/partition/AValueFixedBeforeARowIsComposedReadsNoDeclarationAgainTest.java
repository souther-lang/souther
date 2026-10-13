package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.InvariantChecker;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferedRow;
import souther.compiler.query.OfferingRequest;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a row is composed beside is taken onto the rules of the value, and the value's declaration
 * is not read again for it.
 *
 * <p>A row probing a boundary fixes the number the boundary is on and chooses the rest of the record
 * beside it, under the clause relating the two. Every boundary fixes another number, so a reading of
 * the declaration made with that number in it is a reading per boundary, and the clauses come to the
 * same thing in each of them: the fixed number is one equality stated on top of what they leave. So
 * the declaration is read once, and each fixing is taken onto that reading.
 *
 * <p>Held by counting readings rather than by timing them, and as a comparison of two models with the
 * same declarations: the second has more boundaries on the same field, so it fixes that field at
 * more values. Where each fixing reads the declaration again the second reads it more often; where a
 * fixing is taken on, the two read it alike. That the answers are the same either way is
 * {@code ASettlingReadAgainAndASettlingTakenOnLeaveTheSameConstructionLimitsTest}'s to hold.
 */
class AValueFixedBeforeARowIsComposedReadsNoDeclarationAgainTest {

    private static final String DECLARATIONS = """
            module demo

            data N = Int
                invariant value >= 0 && value <= 100

            data P = { x: N, y: N }
                invariant together = x.value + y.value <= 100

            behavior band : (p: P) -> Int
            """;

    private static final String ONE_BOUNDARY = DECLARATIONS + """
            let band (p) = if p.x.value > 10 then 1 else 0
            """;

    private static final String FIVE_BOUNDARIES = DECLARATIONS + """
            let band (p) =
                if p.x.value > 50 then 5
                else if p.x.value > 40 then 4
                else if p.x.value > 30 then 3
                else if p.x.value > 20 then 2
                else if p.x.value > 10 then 1
                else 0
            """;

    @Test
    void moreValuesFixedOnTheSameFieldReadItsDeclarationNoMoreTimes() {
        Offered one = offered(ONE_BOUNDARY);
        Offered five = offered(FIVE_BOUNDARIES);

        assertTrue(five.rows() > one.rows(),
                () -> "the model with more boundaries offers " + five.rows() + " rows against "
                        + one.rows() + ", so it fixed `x` at no more values and the comparison "
                        + "below says nothing");
        assertEquals(one.readings(), five.readings(),
                () -> "offering " + five.rows() + " rows read the declarations "
                        + five.readings() + " times against " + one.readings() + " for "
                        + one.rows() + ", so a fixed value is being read into the rules again "
                        + "rather than taken onto the reading there is");
    }

    private record Offered(int rows, long readings) {}

    private static Offered offered(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertTrue(compilation.diagnostics().values().stream().allMatch(List::isEmpty),
                () -> "the model under test compiles clean: " + compilation.diagnostics());
        long before = InvariantChecker.readingsMade();
        List<OfferedRow> rows = Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule(compilation.modules().get(0)))
                .rowsByBehavior().getOrDefault("band", List.of());
        return new Offered(rows.size(), InvariantChecker.readingsMade() - before);
    }
}
