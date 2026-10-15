package souther.compiler.numeric;

import souther.compiler.numeric.AffineConstraint.Read;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the rules bound a form at is the same whether or not a premise naming none of the form's
 * positions is merged in to find out it tightens nothing.
 *
 * <p>Such a premise is passed over only where the residual it would leave is bounded by the ranges
 * alone and above what they bound the form at. That is a claim about the arithmetic and not about
 * any model, so it is held against the reading it replaces, over states written at random — and a
 * random state is often one with no value in it that the differences did not notice, which is
 * exactly where a premise naming none of the form can still tighten it.
 *
 * <p>The reading it replaces is written out here: every half-space of every rule, merged into the
 * form, and the residual bounded by the ends and the differences the way the reading bounds any form.
 */
class APremiseNamingNoneOfAFormIsPassedOverOnlyWhereItCouldTightenNothingTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c", "d", "e");
    private static final int STATES = 1000;
    private static final int FORMS_PER_STATE = 12;

    @Test
    void theBoundIsTheOneEveryPremiseMergedInGives() {
        Random random = new Random(2096);
        int compared = 0;
        int byAPremiseNamingNoneOfTheForm = 0;
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
                ExactRatio constant = ExactRatio.of(random.nextInt(13) - 6);
                Merged expected = everyPremiseMergedIn(reading, rules, coefs, constant);

                assertEquals(expected.bound(), reading.most(coefs, constant),
                        () -> "rules " + rules + ", form " + coefs + " + " + constant);
                compared++;
                if (expected.tightenedByOneNamingNoneOfTheForm()) {
                    byAPremiseNamingNoneOfTheForm++;
                }
            }
        }
        assertTrue(compared > STATES, "the states compared were " + compared);
        assertTrue(byAPremiseNamingNoneOfTheForm > 0,
                "no state had a premise naming none of the form tighten it, so whether one that"
                        + " can is merged in was never asked");
    }

    /**
     * A form that weighs one of its positions at nought is one position as far as a residual is
     * concerned, so a premise over one other position leaves a difference, and the differences
     * bound that where the ranges do not. Here {@code b <= 1} names nothing of {@code a + 0·z}, sits
     * well above the least {@code b} comes to, and still takes {@code a} from ten to one through
     * {@code a - b <= 0}.
     */
    @Test
    void aFormWeighingOnePositionIsTightenedThroughTheDifferenceAPremiseLeaves() {
        List<AffineConstraint<String>> rules = List.of(
                stated(Map.of("a", ExactRatio.of(1), "b", ExactRatio.of(-1)), 0),
                stated(Map.of("b", ExactRatio.of(1)), -1));
        Map<String, ExactCut> least = new LinkedHashMap<>();
        least.put("b", ExactCut.inclusive(ExactRatio.of(-5)));
        least.put("z", ExactCut.inclusive(ExactRatio.of(0)));
        Map<String, ExactCut> most = new LinkedHashMap<>();
        most.put("a", ExactCut.inclusive(ExactRatio.of(10)));
        most.put("z", ExactCut.inclusive(ExactRatio.of(0)));
        FormReach<String> reading = FormReach.over(rules, new Box<>(least, most),
                DifferenceBounds.over(rules, CanonicalOrder.asTheyAreSpelled()),
                CanonicalOrder.asTheyAreSpelled());
        Map<String, ExactRatio> form = new LinkedHashMap<>();
        form.put("a", ExactRatio.of(1));
        form.put("z", ExactRatio.of(0));

        assertEquals(ExactCut.inclusive(ExactRatio.of(1)), reading.most(form, ExactRatio.of(0)));
    }

    /** {@code Σ coefs <= -constant}, as the reading states it. */
    private static AffineConstraint<String> stated(Map<String, ExactRatio> coefs, int constant) {
        Read<String> read = AffineConstraint.of(new LinkedHashMap<>(coefs),
                ExactRatio.of(constant), Rel.LE, atom -> Granularity.DISCRETE);
        return ((Read.Stated<String>) read).constraint();
    }

    private record Merged(ExactCut bound, boolean tightenedByOneNamingNoneOfTheForm) {}

    private static Merged everyPremiseMergedIn(FormReach<String> reading,
                                               List<AffineConstraint<String>> rules,
                                               Map<String, ExactRatio> coefs,
                                               ExactRatio constant) {
        ExactCut best = reading.mostFromTheEndsAndTheDifferences(coefs, constant);
        if (coefs.size() <= 1) {
            return new Merged(best, false);
        }
        boolean tightenedByOneNamingNoneOfTheForm = false;
        for (AffineConstraint<String> rule : rules) {
            for (AffineConstraint.HalfSpace<String> premise : rule.halfSpaces()) {
                Map<String, ExactRatio> left = new LinkedHashMap<>(coefs);
                boolean namesNone = true;
                boolean composed = true;
                for (Map.Entry<String, ExactRatio> each
                        : premise.form().entriesIn(CanonicalOrder.asTheyAreSpelled())) {
                    ExactRatio was = left.get(each.getKey());
                    namesNone &= was == null;
                    ExactRatio now = was == null ? each.getValue().negated()
                            : was.plus(each.getValue().negated()).orNull();
                    composed &= now != null;
                    left.put(each.getKey(), now == null ? was : now);
                }
                ExactRatio residualConstant = constant.plus(premise.bound().at()).orNull();
                if (!composed || residualConstant == null) {
                    continue;
                }
                left.values().removeIf(ExactRatio::isZero);
                ExactCut residual =
                        reading.mostFromTheEndsAndTheDifferences(left, residualConstant);
                if (residual != null) {
                    ExactCut tightened = ExactCut.tighterUpper(best, new ExactCut(residual.at(),
                            residual.inclusive() && premise.bound().inclusive()));
                    if (namesNone && !tightened.equals(best)) {
                        tightenedByOneNamingNoneOfTheForm = true;
                    }
                    best = tightened;
                }
            }
        }
        return new Merged(best, tightenedByOneNamingNoneOfTheForm);
    }

    private static List<AffineConstraint<String>> rules(Random random) {
        List<AffineConstraint<String>> rules = new ArrayList<>();
        int count = 1 + random.nextInt(5);
        while (rules.size() < count) {
            Rel rel = List.of(Rel.LE, Rel.LT, Rel.GE, Rel.GT, Rel.EQ).get(random.nextInt(5));
            Read<String> read = AffineConstraint.of(weights(random, 1 + random.nextInt(3)),
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

    /** A form over two to four positions, now and then weighing one of them at nought. */
    private static Map<String, ExactRatio> form(Random random) {
        Map<String, ExactRatio> coefs = weights(random, 2 + random.nextInt(3));
        if (random.nextInt(6) == 0) {
            coefs.replace(coefs.keySet().iterator().next(), ExactRatio.of(0));
        }
        return coefs;
    }

    private static Map<String, ExactRatio> weights(Random random, int positions) {
        List<String> shuffled = new ArrayList<>(POSITIONS);
        Collections.shuffle(shuffled, random);
        Map<String, ExactRatio> out = new LinkedHashMap<>();
        for (String position : shuffled.subList(0, positions)) {
            int weight = 1 + random.nextInt(3);
            out.put(position, ExactRatio.of(random.nextBoolean() ? weight : -weight));
        }
        return out;
    }
}
