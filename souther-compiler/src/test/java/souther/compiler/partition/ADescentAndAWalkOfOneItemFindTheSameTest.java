package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.partition.ScriptedRegion.Script;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A search that goes straight to the end of a walk finds what the walk finds.
 *
 * <p>The two are one search, and the first only skips the readings of the rules on the way to an
 * assignment. Held against the walk over regions written at random: forms of two to five numbers,
 * each run from nought to a ceiling, and rules that refuse assignments holding some of a few
 * patterns. Both kinds of region are written. One shows an assignment empty wherever it holds a
 * pattern, with more fixed or not, narrows each position's run by the patterns, and says its reading
 * is settled. The other shows one empty only while it is exactly a pattern, which is a reading that
 * stops short of the end and does not say it is settled — the walk skips what it showed on the way
 * and the descent has to leave it to the walk.
 *
 * <p>Compared whole: an assignment, or nothing found and why.
 */
class ADescentAndAWalkOfOneItemFindTheSameTest {

    private static final int ITEMS = 1500;

    @Test
    void theDescentAndTheWalkFindTheSame() {
        Random random = new Random(2982);
        int found = 0;
        int readLess = 0;
        int skippedByTheWalk = 0;
        for (int item = 0; item < ITEMS; item++) {
            int count = 2 + random.nextInt(4);
            List<NumericTerm.FromOnePosition> terms = new ArrayList<>();
            for (int i = 0; i < count; i++) {
                terms.add(new NumericTerm.ValueOf(TermPath.of("p.t" + i)));
            }
            int ceiling = 2 + random.nextInt(8);
            int kind = random.nextInt(6);
            List<Map<NumericTerm, Place>> patterns = patterns(random, terms, ceiling);
            Map<NumericTerm, ExactRatio> weights = new LinkedHashMap<>();
            for (NumericTerm.FromOnePosition each : terms) {
                weights.put(each, ExactRatio.of(1 + random.nextInt(2)));
            }
            int level = random.nextInt(ceiling * count + 1);
            Script script = switch (kind) {
                case 4 -> stoppingShort(patterns, ceiling);
                case 5 -> widening(patterns, ceiling);
                default -> monotone(patterns, ceiling);
            };

            ScriptedRegion byTheDescent = ScriptedRegion.of(script);
            ScriptedRegion byTheWalk = ScriptedRegion.of(script);
            Realization descended = realized(new LevelRealizer(), terms, weights, level,
                    byTheDescent);
            Realization walked = realized(new LevelRealizer().walkingOnly(), terms, weights, level,
                    byTheWalk);

            int itemNumber = item;
            assertEquals(walked, descended, () -> "item " + itemNumber + ": " + count
                    + " numbers, level " + level + ", weights " + weights + ", ceiling " + ceiling
                    + ", patterns " + patterns + ", " + List.of("settled", "settled", "settled",
                            "settled", "stopping short", "widening").get(kind));
            if (descended instanceof Realization.Found) {
                found++;
                if (byTheDescent.counts().emptiness.get() < byTheWalk.counts().emptiness.get()) {
                    readLess++;
                }
                if (byTheWalk.counts().fixed.get() > terms.size()) {
                    skippedByTheWalk++;
                }
            }
        }
        assertTrue(found > ITEMS / 4, "items with an assignment found: " + found);
        assertTrue(readLess > found / 8,
                "and of them, those the descent read fewer regions for: " + readLess);
        assertTrue(skippedByTheWalk > 0,
                "and some whose walk fixed more than once per position, having skipped a value");
    }

    private static Realization realized(LevelRealizer realizer,
                                        List<NumericTerm.FromOnePosition> terms,
                                        Map<NumericTerm, ExactRatio> weights, int level,
                                        SearchRegion within) {
        Map<NumericTerm, TermOrders> on = new LinkedHashMap<>();
        TermPath[] paths = new TermPath[terms.size()];
        for (int i = 0; i < terms.size(); i++) {
            on.put(terms.get(i), TermOrdersFixtures.itself(terms.get(i), new Carrier.Whole()));
            paths[i] = TermPath.of("p.t" + i);
        }
        Standing standing = new BorderQuantity.OverAForm("decide",
                new LinearForm<NumericTerm>(ExactRatio.ZERO, weights), on)
                .standingAt(new Criterion.AtTheLevel(Level.OfTheQuantity.of(level)));
        return realizer.realize(standing, within, NothingTheDeclarationsRefuse.at(paths));
    }

    /** One to four patterns, each a value fixed at one or two of the numbers. */
    private static List<Map<NumericTerm, Place>> patterns(Random random,
                                                          List<NumericTerm.FromOnePosition> terms,
                                                          int ceiling) {
        List<Map<NumericTerm, Place>> out = new ArrayList<>();
        for (int i = 0, many = 1 + random.nextInt(4); i < many; i++) {
            Map<NumericTerm, Place> pattern = new LinkedHashMap<>();
            for (int j = 0, size = 1 + random.nextInt(2); j < size; j++) {
                pattern.put(terms.get(random.nextInt(terms.size())),
                        new Count(BigDecimal.valueOf(random.nextInt(ceiling + 1))));
            }
            out.add(pattern);
        }
        return out;
    }

    /**
     * Shown empty wherever a pattern holds, with more fixed or not, and each position running
     * between the least and the greatest value no pattern refuses it.
     */
    private static Script monotone(List<Map<NumericTerm, Place>> patterns, int ceiling) {
        return new Script(standing -> refusedBy(patterns, standing), true,
                (standing, term) -> {
                    Long least = null;
                    Long greatest = null;
                    for (long value = 0; value <= ceiling; value++) {
                        Map<NumericTerm, Place> with = new LinkedHashMap<>(standing);
                        with.put(term, new Count(BigDecimal.valueOf(value)));
                        if (!refusedBy(patterns, with)) {
                            least = least == null ? value : least;
                            greatest = value;
                        }
                    }
                    return least == null ? null : new NumericDomain.Bounds(
                            Endpoint.inclusive(new Count(BigDecimal.valueOf(least))),
                            Endpoint.inclusive(new Count(BigDecimal.valueOf(greatest))));
                });
    }

    /**
     * Shown empty only while the fixed positions are exactly a pattern, which says nothing once
     * another is fixed beside them, and running every position between nought and the ceiling.
     * Not settled, as a reading that stopped short is not.
     */
    private static Script stoppingShort(List<Map<NumericTerm, Place>> patterns, int ceiling) {
        NumericDomain.Bounds whole = new NumericDomain.Bounds(
                Endpoint.inclusive(new Count(BigDecimal.ZERO)),
                Endpoint.inclusive(new Count(BigDecimal.valueOf(ceiling))));
        return new Script(patterns::contains, false, (standing, term) -> whole);
    }

    /**
     * Shown empty wherever a pattern holds, and settled, but running every position from one
     * before anything is fixed and from nought once something is: runs that widen, which the
     * region does not say only narrow.
     */
    private static Script widening(List<Map<NumericTerm, Place>> patterns, int ceiling) {
        NumericDomain.Bounds fromOne = new NumericDomain.Bounds(
                Endpoint.inclusive(new Count(BigDecimal.ONE)),
                Endpoint.inclusive(new Count(BigDecimal.valueOf(ceiling))));
        NumericDomain.Bounds fromNought = new NumericDomain.Bounds(
                Endpoint.inclusive(new Count(BigDecimal.ZERO)),
                Endpoint.inclusive(new Count(BigDecimal.valueOf(ceiling))));
        return new Script(standing -> refusedBy(patterns, standing), true,
                (standing, term) -> standing.isEmpty() ? fromOne : fromNought, false);
    }

    private static boolean refusedBy(List<Map<NumericTerm, Place>> patterns,
                                     Map<NumericTerm, Place> standing) {
        return patterns.stream().anyMatch(pattern ->
                standing.entrySet().containsAll(pattern.entrySet()));
    }
}
