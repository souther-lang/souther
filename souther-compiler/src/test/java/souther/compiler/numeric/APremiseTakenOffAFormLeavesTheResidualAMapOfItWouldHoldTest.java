package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the ends and the differences leave a form once a premise is taken off it is what they leave
 * the map of that residual.
 *
 * <p>The residual is added up as it is made and not held in a map. A sum is exact and can fail part
 * of the way, and whether it does turns on which terms were added before it — so what is held here
 * is the order as well as the value: the positions of the form where they were, then those only the
 * premise names, in the premise's order, with a position weighed nought no term at all. The map it
 * replaces is written out below, and the two are compared over states written at random, a few of
 * them with weights far enough apart in scale that a sum, or a merge of two weights, has no
 * representation.
 */
class APremiseTakenOffAFormLeavesTheResidualAMapOfItWouldHoldTest {

    private static final List<String> POSITIONS =
            List.of("a", "b", "c", "d", "e", "f", "g", "h", "i", "j", "k", "l");
    private static final ExactRatio HUGE = ExactRatio.of(new BigDecimal("1e1500000000"));
    private static final ExactRatio TINY = ExactRatio.of(new BigDecimal("1e-1500000000"));
    private static final int STATES = 1500;
    private static final int FORMS_PER_STATE = 10;

    @Test
    void theResidualComesToWhatTheMapOfItComesTo() {
        Random random = new Random(2682);
        int compared = 0;
        int composed = 0;
        int uncomposed = 0;
        int ofAPremiseNamingManyPositions = 0;
        for (int s = 0; s < STATES; s++) {
            List<AffineConstraint<String>> rules = rules(random);
            DifferenceBounds<String> differences =
                    DifferenceBounds.over(rules, CanonicalOrder.asTheyAreSpelled());
            if (differences.holdsNothing()) {
                continue;
            }
            FormReach<String> reading = FormReach.over(rules, box(random), differences,
                    CanonicalOrder.asTheyAreSpelled());
            for (int f = 0; f < FORMS_PER_STATE; f++) {
                Map<String, ExactRatio> coefs = form(random);
                ExactRatio constant = random.nextInt(20) == 0 ? HUGE
                        : ExactRatio.of(random.nextInt(13) - 6);
                for (AffineConstraint<String> rule : rules) {
                    for (AffineConstraint.HalfSpace<String> premise : rule.halfSpaces()) {
                        ExactCut expected = inAMap(reading, premise, coefs, constant);

                        assertEquals(expected,
                                reading.fromTheEndsWithout(premise, coefs, constant),
                                () -> "premise " + premise + ", form " + coefs + " + " + constant);
                        compared++;
                        if (expected == null) {
                            uncomposed++;
                        } else {
                            composed++;
                        }
                        if (premise.form().coefs().size() > 8) {
                            ofAPremiseNamingManyPositions++;
                        }
                    }
                }
            }
        }
        assertTrue(composed > STATES, "residuals that came to a bound: " + composed);
        assertTrue(uncomposed > 0, "no residual was one the arithmetic could not hold, so the"
                + " failures were never compared");
        assertTrue(ofAPremiseNamingManyPositions > 0,
                "no premise named enough positions to be looked up by index");
        assertTrue(compared > composed + uncomposed - 1);
    }

    /**
     * A residual of nothing at all is the premise's bound alone, and a form the premise cancels
     * to one position is read at that position's end.
     */
    @Test
    void aPremiseThatCancelsTheFormLeavesItsBoundAndOneThatLeavesOnePositionLeavesItsEnd() {
        List<AffineConstraint<String>> rules = List.of(
                stated(Map.of("a", ExactRatio.of(1), "b", ExactRatio.of(1)), -4),
                stated(Map.of("a", ExactRatio.of(1)), -3));
        Map<String, ExactCut> least = new LinkedHashMap<>();
        Map<String, ExactCut> most = new LinkedHashMap<>();
        for (String position : List.of("a", "b")) {
            least.put(position, ExactCut.inclusive(ExactRatio.of(0)));
            most.put(position, ExactCut.inclusive(ExactRatio.of(10)));
        }
        FormReach<String> reading = FormReach.over(rules, new Box<>(least, most),
                DifferenceBounds.over(rules, CanonicalOrder.asTheyAreSpelled()),
                CanonicalOrder.asTheyAreSpelled());
        Map<String, ExactRatio> form = new LinkedHashMap<>();
        form.put("a", ExactRatio.of(1));
        form.put("b", ExactRatio.of(1));
        AffineConstraint.HalfSpace<String> both = rules.get(0).halfSpaces().getFirst();
        AffineConstraint.HalfSpace<String> aAlone = rules.get(1).halfSpaces().getFirst();

        ExactCut cancelled = reading.fromTheEndsWithout(both, form, ExactRatio.ZERO);
        ExactCut leavingB = reading.fromTheEndsWithout(aAlone, form, ExactRatio.ZERO);

        assertEquals(inAMap(reading, both, form, ExactRatio.ZERO), cancelled);
        assertNotNull(cancelled);
        assertEquals(inAMap(reading, aAlone, form, ExactRatio.ZERO), leavingB);
        assertNotNull(leavingB);
    }

    /** Where a weight and the premise's cannot be summed there is no residual. */
    @Test
    void weightsTooFarApartInScaleToBeSummedLeaveNoResidual() {
        List<AffineConstraint<String>> rules = List.of(
                stated(Map.of("a", TINY, "b", ExactRatio.of(1)), 0));
        FormReach<String> reading = FormReach.over(rules, new Box<>(Map.of(), Map.of()),
                DifferenceBounds.over(rules, CanonicalOrder.asTheyAreSpelled()),
                CanonicalOrder.asTheyAreSpelled());
        Map<String, ExactRatio> form = new LinkedHashMap<>();
        form.put("a", HUGE);
        form.put("c", ExactRatio.of(1));
        AffineConstraint.HalfSpace<String> premise = rules.getFirst().halfSpaces().getFirst();

        assertNull(inAMap(reading, premise, form, ExactRatio.ZERO));
        assertNull(reading.fromTheEndsWithout(premise, form, ExactRatio.ZERO));
    }

    /**
     * The map the residual replaces: the form's map copied, the premise's form walked in the one
     * order its positions decide and merged into it, every weight of nought dropped, and the sum
     * of what is left read by the ends and the differences as any map of a form is.
     */
    private static ExactCut inAMap(FormReach<String> reading,
                                   AffineConstraint.HalfSpace<String> premise,
                                   Map<String, ExactRatio> coefs, ExactRatio constant) {
        Map<String, ExactRatio> left = new LinkedHashMap<>(coefs);
        for (Map.Entry<String, ExactRatio> each
                : premise.form().entriesIn(CanonicalOrder.asTheyAreSpelled())) {
            ExactRatio was = left.get(each.getKey());
            if (was == null) {
                left.put(each.getKey(), each.getValue().negated());
            } else if (was.plus(each.getValue().negated()) instanceof ExactAnswer.Held<ExactRatio> sum) {
                left.put(each.getKey(), sum.value());
            } else {
                return null;
            }
        }
        left.values().removeIf(ExactRatio::isZero);
        ExactRatio residualConstant = constant.plus(premise.bound().at()).orNull();
        return residualConstant == null ? null : reading.fromTheEnds(left, residualConstant);
    }

    /** {@code Σ coefs <= -constant}, as the reading states it. */
    private static AffineConstraint<String> stated(Map<String, ExactRatio> coefs, int constant) {
        Read<String> read = AffineConstraint.of(new LinkedHashMap<>(coefs),
                ExactRatio.of(constant), Rel.LE, atom -> Granularity.DISCRETE);
        return ((Read.Stated<String>) read).constraint();
    }

    private static List<AffineConstraint<String>> rules(Random random) {
        List<AffineConstraint<String>> rules = new ArrayList<>();
        int count = 1 + random.nextInt(6);
        while (rules.size() < count) {
            Rel rel = List.of(Rel.LE, Rel.LT, Rel.GE, Rel.GT, Rel.EQ).get(random.nextInt(5));
            int positions = random.nextInt(8) == 0 ? 9 + random.nextInt(3) : 1 + random.nextInt(3);
            Read<String> read = AffineConstraint.of(weights(random, positions, true),
                    ExactRatio.of(random.nextInt(13) - 6), rel, atom -> Granularity.DISCRETE);
            if (read instanceof Read.Stated<String>(AffineConstraint<String> stated)) {
                rules.add(stated);
            }
        }
        return rules;
    }

    /** Ends for some of the positions, some of them open and some of them crossed. */
    private static Box<String> box(Random random) {
        Map<String, ExactCut> least = new LinkedHashMap<>();
        Map<String, ExactCut> most = new LinkedHashMap<>();
        for (String position : POSITIONS) {
            if (random.nextInt(4) > 0) {
                least.put(position, cut(random, random.nextInt(11) - 6));
            }
            if (random.nextInt(4) > 0) {
                most.put(position, cut(random, random.nextInt(11) - 4));
            }
        }
        return new Box<>(least, most);
    }

    private static ExactCut cut(Random random, int at) {
        return random.nextBoolean() ? ExactCut.inclusive(ExactRatio.of(at))
                : ExactCut.exclusive(ExactRatio.of(at));
    }

    /** A form over one to five positions, now and then weighing one of them at nought. */
    private static Map<String, ExactRatio> form(Random random) {
        Map<String, ExactRatio> coefs = weights(random, 1 + random.nextInt(5), true);
        if (random.nextInt(6) == 0) {
            coefs.replace(coefs.keySet().iterator().next(), ExactRatio.of(0));
        }
        return coefs;
    }

    private static Map<String, ExactRatio> weights(Random random, int positions,
                                                   boolean farApartNowAndThen) {
        List<String> shuffled = new ArrayList<>(POSITIONS);
        Collections.shuffle(shuffled, random);
        Map<String, ExactRatio> out = new LinkedHashMap<>();
        for (String position : shuffled.subList(0, positions)) {
            int weight = 1 + random.nextInt(3);
            ExactRatio signed = ExactRatio.of(random.nextBoolean() ? weight : -weight);
            if (farApartNowAndThen && random.nextInt(25) == 0) {
                signed = random.nextBoolean() ? HUGE : TINY;
            }
            out.put(position, signed);
        }
        return out;
    }
}
