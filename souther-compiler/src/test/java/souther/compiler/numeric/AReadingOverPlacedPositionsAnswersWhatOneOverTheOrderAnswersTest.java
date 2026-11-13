package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A domain whose closures are kept walks the forms it is asked about by places worked out for the
 * positions of its rules, and says what a domain keeping nothing says.
 *
 * <p>Held over drawn systems of rules said one at a time, asked after each of them, by three
 * domains that have the same rules: one keeping nothing, one keeping what it is made to by default,
 * and one made to keep so little that what it has is let go and worked out again between
 * questions. What is compared is everything a reader asks — whether the rules leave nothing,
 * whether a form is proved or refuted, how far a form and a position run — so that a place worked
 * out for the wrong positions, a position the table has no place for, or an entry let go and asked
 * again would show as another answer or as a refusal.
 *
 * <p>The systems are drawn to meet what the places depend on: rules over a few positions, so that
 * most are parts of their own; forms over positions of several parts at once; forms naming a
 * position told of and no rule weighs, which a reading answers before it walks anything; and, in
 * one run of the draw, weights and constants far enough apart in scale that a sum of them is one the
 * exact arithmetic comes near holding. What is not held here is that the walk is in the order the
 * domain gives: no answer of these systems turns on it, which is what
 * {@link APlacedOrderWalksAsItsOrderWalksWithoutComparingTest} holds of the order itself.
 *
 * <p>And what is kept is held to what it was made to keep: a run of rules over positions that
 * share none, each asked about together with all those before it, holds no more sets of positions
 * or forms than the table keeps, where a table keeping every one holds the square of the run.
 */
class AReadingOverPlacedPositionsAnswersWhatOneOverTheOrderAnswersTest {

    private static final CanonicalOrder<String> SPELLED = CanonicalOrder.asTheyAreSpelled();

    private static final List<String> POSITIONS = List.of("a", "b", "c", "d", "e", "f");

    /** Told of and weighed by no rule. */
    private static final String UNWEIGHED = "g";

    private static final List<Rel> RELS = List.of(Rel.LE, Rel.GE, Rel.LT, Rel.GT);

    private static final ExactRatio[] SMALL = {
        ExactRatio.of(1), ExactRatio.of(2), ExactRatio.of(3), ExactRatio.of(-1), ExactRatio.of(-2),
        ExactRatio.of(-3)};

    /** Whole numbers near what the exact arithmetic holds and thirds beside them. */
    private static final ExactRatio[] APART_IN_SCALE = {
        ExactRatio.of(1), ExactRatio.of(-1), ExactRatio.of(3),
        ExactRatio.of(7_000_000_000_000_000_000L), ExactRatio.of(-7_000_000_000_000_000_000L),
        ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(3)),
        ExactRatio.of(BigInteger.ONE.negate(), BigInteger.valueOf(3)),
        ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(1_000_000_007L))};

    private static List<String> subsetOf(Random random, List<String> from, int most) {
        List<String> pool = new ArrayList<>(from);
        List<String> out = new ArrayList<>();
        for (int at = 0, count = 1 + random.nextInt(most); at < count && !pool.isEmpty(); at++) {
            out.add(pool.remove(random.nextInt(pool.size())));
        }
        return out;
    }

    private static LinearForm<String> formOf(Random random, List<String> over, ExactRatio[] weights) {
        List<LinearForm<String>> terms = new ArrayList<>();
        for (String each : over) {
            terms.add(LinearForm.weighing(each, weights[random.nextInt(weights.length)]));
        }
        terms.add(LinearForm.constant(weights[random.nextInt(weights.length)]));
        return LinearForm.sum(terms) instanceof ExactAnswer.Held<LinearForm<String>> held
                ? held.value() : null;
    }

    private static Map<String, NumberSpace> spaces() {
        Map<String, NumberSpace> out = new HashMap<>();
        for (String each : POSITIONS) {
            out.put(each, NumberSpace.spacedOnly(Granularity.DISCRETE));
        }
        out.put(UNWEIGHED, NumberSpace.spacedOnly(Granularity.DENSE));
        return out;
    }

    /** What a reader is told, or that it was refused. */
    private static Object told(Supplier<Object> asked) {
        try {
            return asked.get();
        } catch (RuntimeException refused) {
            return "refused: " + refused.getClass().getSimpleName();
        }
    }

    private static List<Object> answersOf(NumericDomain<String> domain, LinearForm<String> form,
                                          Rel rel) {
        return List.of(
                told(domain::isBottom),
                told(() -> domain.entails(form, rel)),
                told(() -> domain.refutes(form, rel)),
                told(() -> domain.boundsOf(form)),
                told(() -> domain.boundsOf("a")));
    }

    private record Domains(List<ClosedStates> closures, List<NumericDomain<String>> domains) {

        static Domains of() {
            List<ClosedStates> closures = List.of(ClosedStates.NONE, ClosedStates.kept(),
                    ClosedStates.keptWithTablesOf(2, 3, ClosureWork.PLACES_KEPT));
            List<NumericDomain<String>> told = new ArrayList<>();
            for (ClosedStates each : closures) {
                told.add(NumericDomain.top(SPELLED, each).told(spaces()));
            }
            return new Domains(closures, told);
        }

        Domains said(LinearForm<String> form, Rel rel) {
            List<NumericDomain<String>> next = new ArrayList<>();
            for (NumericDomain<String> each : domains) {
                next.add(each.assume(form, rel, spaces()));
            }
            return new Domains(closures, next);
        }
    }

    private int drawnAndAsked(ExactRatio[] weights, long seed) {
        Random random = new Random(seed);
        Domains domains = Domains.of();
        int answered = 0;
        for (int rule = 0, rules = 1 + random.nextInt(7); rule < rules; rule++) {
            LinearForm<String> said = formOf(random, subsetOf(random, POSITIONS, 3), weights);
            if (said == null) {
                continue;
            }
            domains = domains.said(said, RELS.get(random.nextInt(RELS.size())));
            for (int question = 0; question < 3; question++) {
                List<String> over = subsetOf(random, POSITIONS, 5);
                if (random.nextInt(3) == 0) {
                    over = new ArrayList<>(over);
                    over.add(UNWEIGHED);
                }
                LinearForm<String> asked = formOf(random, over, weights);
                if (asked == null) {
                    continue;
                }
                Rel rel = RELS.get(random.nextInt(RELS.size()));
                List<Object> keepingNothing = answersOf(domains.domains().get(0), asked, rel);
                for (int other = 1; other < domains.domains().size(); other++) {
                    assertEquals(keepingNothing, answersOf(domains.domains().get(other), asked, rel),
                            "seed " + seed + ", rule " + rule + ", over " + over + ", against the domain"
                                    + " that keeps " + (other == 1 ? "by default" : "almost nothing"));
                }
                answered++;
            }
        }
        return answered;
    }

    @Test
    void whatIsAskedOfDomainsKeepingDifferentlyIsAnsweredAlike() {
        int answered = 0;
        for (long seed = 0; seed < 400; seed++) {
            answered += drawnAndAsked(SMALL, seed);
        }
        assertTrue(answered > 400, "questions asked over the drawn systems: " + answered);
    }

    @Test
    void andAlikeWhereTheWeightsAreSoFarApartThatASumOfThemIsNotHeld() {
        int answered = 0;
        for (long seed = 0; seed < 400; seed++) {
            answered += drawnAndAsked(APART_IN_SCALE, 10_000 + seed);
        }
        assertTrue(answered > 400, "questions asked over the drawn systems: " + answered);
    }

    @Test
    void theDomainKeepingByDefaultWorkedOutPlacesForTheQuestionsItWasAsked() {
        Domains domains = Domains.of();
        Random random = new Random(1);
        LinearForm<String> said = formOf(random, List.of("a", "b"), SMALL);
        domains = domains.said(said, Rel.LE);
        List<String> over = List.of("a", "b", "c");
        answersOf(domains.domains().get(1), formOf(random, over, SMALL), Rel.LE);
        assertTrue(domains.closures().get(1).positionSetsHeld() > 0,
                "sets of positions the places are held of, which is what the walks above ran by");
    }

    private static int[] heldAfterRulesOverPositionsThatShareNone(ClosedStates closures, int rules) {
        NumericDomain<String> domain = NumericDomain.top(SPELLED, closures);
        List<LinearForm<String>> atoms = new ArrayList<>();
        for (int at = 1; at <= rules; at++) {
            String name = "x" + at;
            domain = domain.assume(LinearForm.atom(name), Rel.GE,
                    Map.of(name, NumberSpace.spacedOnly(Granularity.DISCRETE)));
            atoms.add(LinearForm.atom(name));
            if (at >= 2) {
                domain.boundsOf(((ExactAnswer.Held<LinearForm<String>>) LinearForm.sum(atoms)).value());
            }
        }
        return new int[] {closures.positionSetsHeld(), closures.walksHeld()};
    }

    @Test
    void whatIsHeldOverARunOfRulesOverPositionsThatShareNoneIsWhatTheTableWasMadeToKeep() {
        int[] kept = heldAfterRulesOverPositionsThatShareNone(
                ClosedStates.keptWithTablesOf(8, 16, ClosureWork.PLACES_KEPT), 60);
        assertTrue(kept[0] <= 8, "sets of positions held: " + kept[0]);
        assertTrue(kept[1] <= 16, "forms whose walk is held: " + kept[1]);

        int[] byDefault = heldAfterRulesOverPositionsThatShareNone(ClosedStates.kept(), 60);
        assertTrue(byDefault[0] > 8 && byDefault[1] > 16,
                "the same run holds more where more is kept, so what is counted is what is held: "
                        + byDefault[0] + " sets, " + byDefault[1] + " forms");
    }

    @Test
    void aWalkThatIsRefusedIsNotCountedAsWorkedOutAndIsAskedAgain() {
        ClosedStates kept = ClosedStates.kept();
        CanonicalOrder<String> keeping = kept.kept(SPELLED);
        CanonicalForm<String> form = new CanonicalForm<>(Map.of("a", ExactRatio.ONE));

        assertThrows(IllegalStateException.class, () -> keeping.walkOf(form, () -> {
            throw new IllegalStateException("two positions are one to the order");
        }));
        assertEquals(0, kept.walksWorkedOut(), "walks counted as worked out that were refused");
        assertEquals(0, kept.walksHeld());

        keeping.walkOf(form, () -> List.of(Map.entry("a", ExactRatio.ONE)));
        assertEquals(1, kept.walksWorkedOut());
    }

    @Test
    void theOrdersTheWalksAreKeptForAreNoMoreThanTheTableWasMadeToKeep() {
        ClosedStates kept = ClosedStates.kept();
        for (int at = 0; at < 100; at++) {
            int written = at;
            // Each is an order of its own, as one written afresh at every call is.
            CanonicalOrder<String> order = (one, other) -> one.compareTo(other) + 0 * written;
            kept.kept(order);
        }
        assertTrue(kept.ordersHeld() <= ClosedStates.ORDERS_KEPT,
                "orders the walks are kept for: " + kept.ordersHeld());
    }

    @Test
    void whereNothingIsKeptNoRuleIsReadForPositionsAndTheOrderIsTheDomainsOwn() {
        Supplier<Set<String>> notAsked = () -> {
            throw new AssertionError("the positions of the rules were read where nothing is kept");
        };
        assertSame(SPELLED, ClosedStates.NONE.placing(notAsked, SPELLED));
        assertSame(SPELLED, ClosedStates.IN_ONE_RUN.placing(notAsked, SPELLED));
    }

    @Test
    void whereClosuresAreKeptThePositionsAreReadWhenAWalkFirstPutsTwoInOrderAndOnce() {
        AtomicInteger read = new AtomicInteger();
        CanonicalOrder<String> placed = ClosedStates.kept().placing(() -> {
            read.incrementAndGet();
            return Set.of("a", "b", "c");
        }, SPELLED);

        assertEquals(0, read.get(), "positions read for an order nobody has walked with");
        placed.walking(Map.of("a", ExactRatio.ONE).entrySet(), Map.Entry::getKey);
        assertEquals(0, read.get(), "positions read for a walk of one position");
        placed.walking(Map.of("a", ExactRatio.ONE, "b", ExactRatio.ONE).entrySet(), Map.Entry::getKey);
        placed.walking(Map.of("c", ExactRatio.ONE, "b", ExactRatio.ONE).entrySet(), Map.Entry::getKey);
        assertEquals(1, read.get(), "times the positions were read for walks of two positions");
    }
}
