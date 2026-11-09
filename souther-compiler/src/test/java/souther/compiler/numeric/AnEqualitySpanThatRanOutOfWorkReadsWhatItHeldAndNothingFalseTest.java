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
            return new EqualitySpan.Residue<>(Map.of(), constant.negated());
        }
        return span.residue(new CanonicalForm<>(sum), constant.negated());
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
