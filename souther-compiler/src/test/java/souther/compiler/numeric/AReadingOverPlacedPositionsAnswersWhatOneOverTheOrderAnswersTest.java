package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.Set;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A domain whose closures are kept walks the forms it is asked about by the places its parts were
 * asked with, and says what a domain keeping nothing says.
 *
 * <p>Held over drawn systems of rules said one at a time, asked after each of them, by three
 * domains that have the same rules: one keeping nothing, one keeping what it is made to by default,
 * and one made to keep so little that what it has is let go and worked out again between
 * questions. What is compared is everything a reader asks — whether the rules leave nothing,
 * whether a form is proved or refuted, how far a form and a position run — so that a walk by the
 * places of the wrong part, a position the part has no place for, or an entry let go and asked
 * again would show as another answer or as a refusal.
 *
 * <p>The systems are drawn to meet what the places depend on: rules over a few positions, so that
 * most are parts of their own; forms over positions of several parts at once; forms naming a
 * position told of and no rule weighs, which a reading answers before it walks anything; and, in
 * one run of the draw, weights and constants far enough apart in scale that a sum of them is one the
 * exact arithmetic comes near holding. What is not held here is that the walk is in the order the
 * domain gives: no answer of these systems turns on it, which is what
 * {@link APartedOrderWalksAsItsOrderWalksWithoutComparingTest} holds of the order itself.
 *
 * <p>And what is kept is held to what it was made to keep: tables of sets of positions, of forms
 * walked and of orders hold no more than they were made to over a long run of rules; a reading
 * puts no set of positions to the table beside those of the closures; and a form of two positions
 * over many rules that share none is put in order by a number of comparisons that does not grow
 * with the rules.
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
            // Each is an order of its own, as one written afresh at every call is.
            kept.kept(new SpelledAfresh());
        }
        assertTrue(kept.ordersHeld() <= ClosedStates.ORDERS_KEPT,
                "orders the walks are kept for: " + kept.ordersHeld());
    }

    /** The spelling order, as an object of its own each time one is made. */
    private static final class SpelledAfresh implements CanonicalOrder<String> {

        @Override
        public int compare(String one, String other) {
            return one.compareTo(other);
        }
    }

    @Test
    void aFormOverTwoPositionsOfManyRulesThatShareNoneIsNotPutInOrderByComparingEveryPosition() {
        int few = comparisonsToAskTwoPositionsOfRulesOverPositionsThatShareNone(50);
        int many = comparisonsToAskTwoPositionsOfRulesOverPositionsThatShareNone(800);
        assertTrue(many <= few + 20,
                "comparisons for a form of two positions grew with the rules: " + few + " over 50, "
                        + many + " over 800");
    }

    private static int comparisonsToAskTwoPositionsOfRulesOverPositionsThatShareNone(int rules) {
        AtomicInteger compared = new AtomicInteger();
        CanonicalOrder<String> counting = (one, other) -> {
            compared.incrementAndGet();
            return one.compareTo(other);
        };
        NumericDomain<String> domain = NumericDomain.top(counting, ClosedStates.kept());
        for (int at = 1; at <= rules; at++) {
            String name = "x" + at;
            Map<String, NumberSpace> spaces = Map.of(name, NumberSpace.spacedOnly(Granularity.DISCRETE));
            // Both ends, so that a form over the position is one the reading goes on to put in order
            // and not one it answers as unbounded before it walks anything.
            domain = domain.assume(LinearForm.atom(name), Rel.GE, spaces);
            domain = domain.assume(LinearForm.atomMinusConstant(name, ExactRatio.of(10)), Rel.LE, spaces);
        }
        List<LinearForm<String>> two = List.of(LinearForm.atom("x1"), LinearForm.atom("x2"));
        LinearForm<String> sum = ((ExactAnswer.Held<LinearForm<String>>) LinearForm.sum(two)).value();
        // What is asked is the form of two positions; the closure of the rules is worked out for it
        // first, which is the same however it is walked, so it is asked for before the count starts.
        assertFalse(domain.isBottom());
        compared.set(0);
        assertNotNull(domain.boundsOf(sum).max(), "the form is one the reading put in order to bound");
        return compared.get();
    }

    @Test
    void thePlacesOfPositionsAskedInTheirOrderAreWorkedOutByAsManyComparisonsAsThereArePositions() {
        AtomicInteger compared = new AtomicInteger();
        CanonicalOrder<String> counting = (one, other) -> {
            compared.incrementAndGet();
            return one.compareTo(other);
        };
        Set<String> inOrder = new LinkedHashSet<>();
        for (int at = 0; at < 500; at++) {
            inOrder.add("p" + String.format("%04d", at));
        }

        ClosedStates kept = ClosedStates.kept();
        kept.placed(inOrder, counting);
        assertTrue(compared.get() <= 2 * inOrder.size(),
                "comparisons to place " + inOrder.size() + " positions that came in their order: "
                        + compared.get());

        compared.set(0);
        kept.placed(inOrder, counting);
        assertEquals(0, compared.get(), "comparisons to place the positions of a set already placed");
    }

    @Test
    void theSetsOfPositionsHeldAreThoseTheClosuresWereAskedAndNoSetOfARead() {
        ClosedStates kept = ClosedStates.kept();
        NumericDomain<String> domain = NumericDomain.top(SPELLED, kept);
        List<NumericDomain<String>> held = new ArrayList<>();
        List<LinearForm<String>> atoms = new ArrayList<>();
        Map<String, NumberSpace> spaces = new HashMap<>();
        for (int at = 1; at <= 40; at++) {
            String name = "x" + at;
            spaces.put(name, NumberSpace.spacedOnly(Granularity.DISCRETE));
            atoms.add(LinearForm.atom(name));
            domain = domain.assume(LinearForm.atom(name), Rel.GE, spaces);
            List<LinearForm<String>> withConstant = new ArrayList<>(atoms);
            withConstant.add(LinearForm.constant(ExactRatio.of(-1000)));
            domain = domain.assume(
                    ((ExactAnswer.Held<LinearForm<String>>) LinearForm.sum(withConstant)).value(),
                    Rel.LE, spaces);
            if (at >= 2) {
                domain.boundsOf(((ExactAnswer.Held<LinearForm<String>>) LinearForm.sum(atoms)).value());
            }
            held.add(domain);
        }
        assertEquals(40, held.size());
        assertTrue(kept.positionSetsHeld() <= kept.workedOut(),
                "sets of positions held, " + kept.positionSetsHeld() + ", for closures worked out, "
                        + kept.workedOut() + ": a reading worked out places of its own");
    }
}
