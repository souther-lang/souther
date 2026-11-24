package souther.compiler.numeric;

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
 * Where the work of reading a set of equalities runs out, the equalities reached before it did are
 * what is read, and what is shown from them is shown of the whole set. Which equalities were
 * reached is the order they were stated in, so a set stated otherwise may be read further or less
 * far: that is the one thing here that turns on anything but the equalities, and it is said of
 * a reading short of its work, never of one that finished.
 */
class AnEqualitySpanThatRanOutOfWorkReadsWhatItHeldAndNothingFalseTest {

    private static final String[] NAMES = {"a", "b", "c", "d", "e"};

    private static AffineConstraint<String> equality(Random random) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        for (int i = 0, size = 2 + random.nextInt(3); i < size; i++) {
            int weight = random.nextInt(5) - 2;
            coefs.merge(NAMES[random.nextInt(NAMES.length)],
                    ExactRatio.of(weight == 0 ? 1 : weight), (x, y) -> x.plus(y).orNull());
        }
        coefs.values().removeIf(ExactRatio::isZero);
        if (coefs.isEmpty()) {
            coefs.put(NAMES[0], ExactRatio.ONE);
        }
        return new AffineConstraint.Equality<>(new CanonicalForm<>(coefs),
                ExactRatio.of(random.nextInt(5) - 2));
    }

    private static boolean nothing(EqualitySpan.Residue<String> left) {
        return left != null && left.coefs().isEmpty() && left.constant().isZero();
    }

    /** A combination of some of the equalities, which every reading that holds them shows. */
    private static EqualitySpan.Residue<String> readAsTheSumOf(EqualitySpan<String> span,
                                                              List<AffineConstraint<String>> some) {
        Map<String, ExactRatio> sum = new LinkedHashMap<>();
        ExactRatio constant = ExactRatio.ZERO;
        for (AffineConstraint<String> each : some) {
            AffineConstraint.Equality<String> equality = (AffineConstraint.Equality<String>) each;
            for (Map.Entry<String, ExactRatio> entry : equality.form().entriesIn(
                    CanonicalOrder.asTheyAreSpelled())) {
                sum.merge(entry.getKey(), entry.getValue(), (x, y) -> x.plus(y).orNull());
            }
            constant = constant.minus(equality.at()).orNull();
        }
        sum.values().removeIf(ExactRatio::isZero);
        if (sum.isEmpty()) {
            return new EqualitySpan.Residue<>(Map.of(), constant);
        }
        return span.residue(new CanonicalForm<>(sum), constant);
    }

    private static AffineConstraint<String> pinned(String position, int at) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        coefs.put(position, ExactRatio.ONE);
        return new AffineConstraint.Equality<>(new CanonicalForm<>(coefs), ExactRatio.of(at));
    }

    /** The oracle itself: {@code x = 2} and {@code y = 3} make {@code x + y - 5} nothing and
     *  {@code x + y + 5} something, so a sum read with its constant the wrong way round would show
     *  nothing true and every property over it would hold by there being nothing to find. */
    @Test
    void aSumOfEqualitiesIsNothingAtTheConstantTheyComeToAndNotAtItsNegation() {
        List<AffineConstraint<String>> two = List.of(pinned("x", 2), pinned("y", 3));
        EqualitySpan<String> span = EqualitySpan.of(two, CanonicalOrder.asTheyAreSpelled());

        assertTrue(nothing(readAsTheSumOf(span, two)));
        Map<String, ExactRatio> both = new LinkedHashMap<>();
        both.put("x", ExactRatio.ONE);
        both.put("y", ExactRatio.ONE);
        assertTrue(!nothing(span.residue(new CanonicalForm<>(both), ExactRatio.of(5))),
                "x + y + 5 is not what x = 2 and y = 3 make nothing");
    }

    /**
     * An equality no position of which can be solved for costs the work it is given and no more:
     * weights of two sizes too far apart to divide one by another make every position fail, and
     * trying them is counted with the rest, so a set of such equalities is not more work than the
     * span may spend however wide they are.
     */
    @Test
    void tryingEveryPositionOfAnEqualityNoPositionCanBeSolvedForIsCountedAsWork() {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        for (int i = 0; i < 200; i++) {
            coefs.put("p" + i, ExactRatio.tenTo(i % 2 == 0 ? Long.MIN_VALUE : Long.MAX_VALUE));
        }
        List<AffineConstraint<String>> rules = List.of(
                new AffineConstraint.Equality<>(new CanonicalForm<>(coefs), ExactRatio.ZERO),
                pinned("x", 2));

        EqualitySpan<String> plenty = EqualitySpan.of(rules, CanonicalOrder.asTheyAreSpelled());
        EqualitySpan<String> short_ = EqualitySpan.of(rules, CanonicalOrder.asTheyAreSpelled(), 50);

        assertTrue(plenty != null, "left out and the next equality read, where the work suffices");
        assertEquals(null, short_, "nothing is read where trying the positions spent the work");
    }

    /**
     * A sum of equalities is shown to come to nothing by a reading short of its work only where it
     * does: shown of the equalities held, so of the whole set, and the whole set shows it too.
     */
    @Test
    void whatAReadingShortOfItsWorkShowsTheWholeReadingShows() {
        Random random = new Random(41);
        int shown = 0;
        List<String> wrong = new ArrayList<>();
        for (int round = 0; round < 200; round++) {
            List<AffineConstraint<String>> rules = new ArrayList<>();
            for (int i = 0; i < 6; i++) {
                rules.add(equality(random));
            }
            EqualitySpan<String> whole =
                    EqualitySpan.of(rules, CanonicalOrder.asTheyAreSpelled());
            for (int budget = 0; budget <= 12; budget++) {
                EqualitySpan<String> short_ =
                        EqualitySpan.of(rules, CanonicalOrder.asTheyAreSpelled(), budget);
                if (short_ == null || whole == null) {
                    continue;
                }
                for (int i = 0; i < rules.size(); i++) {
                    for (int j = i + 1; j < rules.size(); j++) {
                        List<AffineConstraint<String>> two = List.of(rules.get(i), rules.get(j));
                        if (nothing(readAsTheSumOf(short_, two))) {
                            shown++;
                            if (!nothing(readAsTheSumOf(whole, two))) {
                                wrong.add("budget " + budget + " shows " + two + " and the whole"
                                        + " does not");
                            }
                        }
                    }
                }
            }
        }
        assertEquals(List.of(), wrong);
        assertTrue(shown > 0, "nothing was shown, so nothing was held to the whole");
    }

    /** With the work to read all of it, the equalities stated in any order are read alike. */
    @Test
    void aSetReadInFullIsReadTheSameInAnyOrderItIsStatedIn() {
        Random random = new Random(43);
        for (int round = 0; round < 100; round++) {
            List<AffineConstraint<String>> rules = new ArrayList<>();
            for (int i = 0; i < 5; i++) {
                rules.add(equality(random));
            }
            List<AffineConstraint<String>> other = new ArrayList<>(rules);
            Collections.shuffle(other, random);
            EqualitySpan<String> one = EqualitySpan.of(rules, CanonicalOrder.asTheyAreSpelled());
            EqualitySpan<String> two = EqualitySpan.of(other, CanonicalOrder.asTheyAreSpelled());
            assertEquals(one == null, two == null, "read in one order and not in another");
            if (one == null) {
                continue;
            }
            for (int i = 0; i < rules.size(); i++) {
                for (int j = i + 1; j < rules.size(); j++) {
                    List<AffineConstraint<String>> pair = List.of(rules.get(i), rules.get(j));
                    assertEquals(nothing(readAsTheSumOf(one, pair)),
                            nothing(readAsTheSumOf(two, pair)));
                }
            }
        }
    }
}
