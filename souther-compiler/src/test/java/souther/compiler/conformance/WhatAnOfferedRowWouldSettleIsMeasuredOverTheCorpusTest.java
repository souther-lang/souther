package souther.compiler.conformance;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.OfferItem;
import souther.compiler.query.Composition;
import souther.compiler.query.OfferingRequest;
import souther.compiler.query.RowKey;
import souther.compiler.query.Settlement;
import souther.compiler.query.Settlements;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What every row the corpus is offered would settle, counted over the whole of it.
 *
 * <p>The table this is about is what a reduction of the offering would act on, and a reduction acts
 * only on what a row is known to settle. So the two things worth holding are that the walk answers
 * for the whole table — every row against every item the run was asked about — and that what it
 * cannot tell stays told apart from what it read and found not to be the case.
 *
 * <p>The numbers are printed rather than pinned. What the corpus happens to hold moves as the corpus
 * is written, and a checked-in count would be a snapshot of the models rather than of this walk.
 * What is asserted is the shape: the table is total, the items are what was asked for, and no row
 * composed for something is read as not settling it.
 *
 * <p><b>Of this corpus, and not of every model.</b> Over souther-examples that last one does not
 * hold: twenty-four points there have a row composed at them that this walk reads as standing
 * somewhere else, which is the search and this reading of one model coming to two answers. It costs
 * no row — what a row was composed for keeps it whatever this walk can tell — but it is a
 * disagreement, and it is written down here rather than left to be found by whoever strengthens the
 * assertion next.
 */
class WhatAnOfferedRowWouldSettleIsMeasuredOverTheCorpusTest {

    @Test
    void everyOfferedRowIsAnsweredForAtEveryItemTheRunWasAskedAbout() {
        Map<String, Integer> answers = new TreeMap<>();
        Map<String, Integer> undetermined = new TreeMap<>();
        int rows = 0;
        int items = 0;
        int settledNotComposedFor = 0;
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            ConformanceCorpus.Analysed analysed = corpus.analyse();
            for (String module : analysed.compilation().modules()) {
                java.util.Map<String, Adequacy.Filling> filled =
                        Adequacy.generatedOf(analysed.compilation().db(), module);
                if (filled == null) {
                    continue;
                }
                // The composition, because what a row was composed for is a fact about it: read
                // off what a person is finally handed, a row another row answers for is not there
                // to be asked about.
                Composition offering = Composition.composed(
                        OfferingRequest.overTheModule(module, true), filled,
                        Adequacy.generatedForDeclarationsOf(analysed.compilation().db(), module,
                                new souther.compiler.query.GenerationScope.Module()));
                Settlements settlements =
                        Settlements.of(analysed.compilation().db(), offering);
                rows += settlements.byRow().size();
                items += settlements.requested().size();

                // Total over the two axes it names. A pair with no entry is a row nobody asked
                // about at an item, and a reduction reading that absence would be free to read it
                // either way.
                for (Map.Entry<RowKey, Map<OfferItem, Settlement>> row
                        : settlements.byRow().entrySet()) {
                    assertEquals(new LinkedHashSet<>(settlements.requested()),
                            row.getValue().keySet(),
                            "every item this run was asked about is answered for " + row.getKey());
                    row.getValue().forEach((item, settlement) -> {
                        answers.merge(kindOf(item) + " " + nameOf(settlement), 1, Integer::sum);
                        if (settlement instanceof Settlement.Undetermined(var why)) {
                            undetermined.merge(why.name(), 1, Integer::sum);
                        }
                    });
                }

                // What the searches composed a row for, against what the rows turn out to settle.
                // A row composed for an item and read as not settling it is the generator and this
                // walk reading one model two ways. Held of this corpus: over souther-examples there
                // are points where the two disagree, which is said above.
                settlements.composedFor().forEach((item, row) -> {
                    Map<OfferItem, Settlement> here = settlements.byRow().get(row);
                    if (here != null) {
                        assertFalse(here.get(item) instanceof Settlement.DoesNotSettle,
                                "a row composed for " + item + " does not settle it: " + row);
                    }
                });
                Set<OfferItem> settled = settlements.settled();
                for (OfferItem item : settled) {
                    if (!settlements.composedFor().containsKey(item)) {
                        settledNotComposedFor++;
                    }
                }
                assertTrue(settlements.requested().containsAll(settled),
                        "nothing is settled that was not asked about");
            }
        }
        System.out.println("rows " + rows + ", items " + items
                + ", settled with no row composed for them " + settledNotComposedFor);
        System.out.println("answers " + answers);
        System.out.println("undetermined " + undetermined);
        assertTrue(rows > 0, "the corpus offers rows");
        assertTrue(items > 0, "and is asked for something");
    }

    private static String kindOf(OfferItem item) {
        return switch (item) {
            case OfferItem.AClass _ -> "class";
            case OfferItem.AnArm _ -> "arm";
            case OfferItem.APointOfALine _ -> "point";
        };
    }

    private static String nameOf(Settlement settlement) {
        return switch (settlement) {
            case Settlement.Settles _ -> "settles";
            case Settlement.DoesNotSettle _ -> "does not";
            case Settlement.Undetermined _ -> "undetermined";
        };
    }
}
