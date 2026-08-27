package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.GenerationScope;
import souther.compiler.query.OfferItem;
import souther.compiler.query.Offering;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.OwedBoundaryPoint;
import souther.compiler.query.RowKey;
import souther.compiler.query.Settlements;
import souther.compiler.partition.BorderObligationPoint;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two things owed at one point are two items, however many rows they take.
 *
 * <p>A region is stopped by whatever reaches the position, and where two rules stop it in two places
 * the line is owed a row in that role twice — two obligations at one point of one line. One value
 * answers both, which is why the search composes one row for them; the account is what says there
 * are two.
 *
 * <p><b>Those are two questions and only one of them is about rows.</b> Read as the places a row is
 * composed at, the second obligation is in no item universe: nothing counts a row as settling it,
 * nothing can say it is answered, and a note saying no row is offered for it prints over the row
 * standing at it. That is the shape this whole change is against, arriving from the inside.
 */
class EveryThingOwedAtAPointIsAnItemOfItsOwnTest {

    /**
     * One position whose line is stopped in two places.
     *
     * <p>Two helpers compare the same position at the same value, so the region beside the
     * declaration's line runs up to a line each of them drew. The values coincide; the rules do not.
     */
    private static final String TWO_STOPS = """
            module example.stops

            data Hours = Int
                invariant value >= 0 && value <= 24

            let over (h: Hours): Int = if h.value > 8 then 1 else 0

            let also (h: Hours): Int = if h.value > 8 then 2 else 0

            behavior tally : (worked: Hours) -> Int

            let tally (worked) = over(worked) + also(worked)
            """;

    @Test
    void aPointOwedTwiceIsTwoItemsOfTheOffering() {
        Compilation compilation = compiled();
        List<BorderAssessment> edges = compilation.db()
                .ask(new Adequacy.BoundarySearch("example.stops", "tally")).value();
        assertNotNull(edges, "the model under test is measured");
        List<OwedBoundaryPoint> account = OwedBoundaryPoint.across(edges);
        assertTrue(account.size() > OwedBoundaryPoint.oneForEachPoint(account).at().size(),
                "the model under test owes some point more than once: " + account);

        Settlements table = Settlements.of(compilation.db(), composed(compilation));
        List<BorderObligationPoint> asked = new ArrayList<>();
        for (OfferItem item : table.requested()) {
            if (item instanceof OfferItem.APointOfALine(var point)) {
                asked.add(point);
            }
        }
        // The behavior's own account, entry for entry, before the points the declarations own. Two
        // of these differ in nothing a row is composed or labelled from, and one row answers both:
        // asked as the places a row is composed at, there would be ten of them here.
        List<BorderObligationPoint> owed = account.stream().map(OwedBoundaryPoint::owed).toList();
        assertTrue(asked.size() >= owed.size(), "every point of the account is asked about: " + asked);
        assertEquals(owed, asked.subList(0, owed.size()),
                "every thing owed at a point is asked about, and not one per point");
    }

    @Test
    void theTwoOfThemAreAnsweredByTheOneRowComposedThere() {
        Compilation compilation = compiled();
        Settlements table = Settlements.of(compilation.db(), composed(compilation));

        // The obligations that share a point, which is what a row there answers at once.
        Map<String, Set<OfferItem>> byPoint = new LinkedHashMap<>();
        for (OfferItem item : table.requested()) {
            if (item instanceof OfferItem.APointOfALine(var point)) {
                byPoint.computeIfAbsent(point.line() + " " + point.role(),
                        _ -> new LinkedHashSet<>()).add(item);
            }
        }
        List<Set<OfferItem>> shared = byPoint.values().stream().filter(at -> at.size() > 1).toList();
        assertFalse(shared.isEmpty(), "a point of this model is owed more than once: " + byPoint);

        for (Set<OfferItem> at : shared) {
            Set<RowKey> composedThere = new LinkedHashSet<>();
            at.forEach(item -> composedThere.add(table.composedFor().get(item)));
            assertEquals(1, composedThere.size(),
                    "one row is composed for everything owed at one point: " + at + " -> "
                            + composedThere);
            // And it answers all of them, so a reduction counts it once for each.
            RowKey row = composedThere.iterator().next();
            if (row != null) {
                at.forEach(item -> assertTrue(table.at(row, item).settles(),
                        "the row composed there settles " + item));
            }
        }
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(TWO_STOPS, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static Offering composed(Compilation compilation) {
        Map<String, Adequacy.Filling> generated =
                Adequacy.generatedOf(compilation.db(), "example.stops");
        assertNotNull(generated, "the model under test compiles: " + compilation.errors());
        return Offering.composed(OfferingRequest.overTheModule("example.stops", true), generated,
                Adequacy.generatedForDeclarationsOf(compilation.db(), "example.stops",
                        new GenerationScope.Module()));
    }
}
