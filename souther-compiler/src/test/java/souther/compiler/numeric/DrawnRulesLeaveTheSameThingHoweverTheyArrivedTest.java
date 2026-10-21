package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.test.Nightly;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a domain says of rules drawn at random is a function of the rules, and not of the order they
 * arrived in or how often each was said.
 *
 * <p>The claim is the last one of {@code TheSameRulesLeaveTheSameThingHoweverTheyArrivedTest}: the
 * same rules shuffled or said twice leave the same ranges and prove and refuse the same things, and
 * a question scaled up is the same question. The systems there are chosen for the readers that could
 * let one rule's place in the list decide, and are given in every order. These are drawn over
 * weights from minus two to two on each of three positions, every relation and every threshold in
 * the range, and shuffled once each, which reaches combinations of rules no chosen system names. The
 * seed is fixed, so a round that fails is the same round when it is run again.
 *
 * <p>Nightly, for what it costs: hundreds of draws, each said into three domains. No cheaper way asks
 * whether some combination the chosen systems do not name makes the order matter, and what it finds
 * is as well found by the morning as by the change that caused it, since the chosen systems stand in
 * the run every change waits on.
 */
@Nightly
class DrawnRulesLeaveTheSameThingHoweverTheyArrivedTest {

    private record Written(LinearForm<String> form, Rel rel) {}

    private static LinearForm<String> num(long n) {
        return LinearForm.constant(ExactRatio.of(n));
    }

    private static LinearForm<String> scaled(String a, long k) {
        return LinearForm.weighing(a, ExactRatio.of(k));
    }

    private static Map<String, Granularity> whole(String... atoms) {
        Map<String, Granularity> out = new LinkedHashMap<>();
        for (String each : atoms) {
            out.put(each, Granularity.DISCRETE);
        }
        return out;
    }

    private static NumericDomain<String> given(List<Written> rules, Map<String, Granularity> kinds) {
        NumericDomain<String> out = NumericDomain.top(CanonicalOrder.asTheyAreSpelled());
        for (Written each : rules) {
            out = out.assume(each.form(), each.rel(), kinds);
        }
        return out;
    }

    @Test
    void theOrderAndTheRepetitionAreNotPartOfAnyAnswer() {
        Map<String, Granularity> kinds = whole("a", "b", "c");
        Random dice = new Random(891);
        for (int round = 0; round < 300; round++) {
            List<Written> rules = someRules(dice);
            NumericDomain<String> asWritten = given(rules, kinds);

            List<Written> shuffled = new ArrayList<>(rules);
            Collections.shuffle(shuffled, dice);
            NumericDomain<String> reordered = given(shuffled, kinds);

            List<Written> doubled = new ArrayList<>(rules);
            doubled.addAll(rules);
            NumericDomain<String> twice = given(doubled, kinds);

            // The same questions, scaled up, are the same questions.
            for (Written each : rules) {
                LinearForm<String> doubledForm =
                        SmallForm.small(each.form()).times(ExactRatio.of(3)).form();
                assertEquals(asWritten.entails(each.form(), each.rel()),
                        asWritten.entails(doubledForm, each.rel()),
                        () -> "scaling the question moved what is proven: " + rules);
                assertEquals(asWritten.refutes(each.form(), each.rel()),
                        asWritten.refutes(doubledForm, each.rel()),
                        () -> "scaling the question moved what is refuted: " + rules);
                assertEquals(asWritten.provenByTheBoxAndItsDifferences(each.form(), each.rel()),
                        asWritten.provenByTheBoxAndItsDifferences(doubledForm, each.rel()),
                        () -> "scaling the question moved what the ranges state: " + rules);
            }
            for (NumericDomain<String> other : List.of(reordered, twice)) {
                assertEquals(asWritten.isBottom(), other.isBottom(),
                        () -> "whether anything is left moved: " + rules);
                for (String position : List.of("a", "b", "c")) {
                    assertEquals(asWritten.boundsOf(position), other.boundsOf(position),
                            () -> "the range at " + position + " moved: " + rules);
                }
                for (Written each : rules) {
                    assertEquals(asWritten.entails(each.form(), each.rel()),
                            other.entails(each.form(), each.rel()),
                            () -> "what is proven moved: " + rules);
                    assertEquals(asWritten.refutes(each.form(), each.rel()),
                            other.refutes(each.form(), each.rel()),
                            () -> "what is refuted moved: " + rules);
                }
            }
        }
    }

    private static List<Written> someRules(Random dice) {
        List<String> positions = List.of("a", "b", "c");
        List<Written> out = new ArrayList<>();
        int howMany = 2 + dice.nextInt(4);
        for (int i = 0; i < howMany; i++) {
            LinearForm<String> form = num(dice.nextInt(15) - 7);
            for (String position : positions) {
                int weight = dice.nextInt(5) - 2;
                if (weight != 0) {
                    form = SmallForm.small(form).plus(scaled(position, weight)).form();
                }
            }
            if (form.coefs().isEmpty()) {
                continue;
            }
            Rel rel = switch (dice.nextInt(6)) {
                case 0 -> Rel.LT;
                case 1 -> Rel.GE;
                case 2 -> Rel.GT;
                case 3 -> Rel.EQ;
                case 4 -> Rel.NE;
                default -> Rel.LE;
            };
            out.add(new Written(form, rel));
        }
        return out;
    }
}
