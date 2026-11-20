package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TwoIntegerConstraints.Constraint;
import souther.compiler.inputs.TwoIntegerConstraints.Shadow;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Which values of one number have a whole number of the other beside them is what counting says,
 * over every system of a sample whose values all lie in a small box: a run exactly where the values
 * counted are a run, nothing where there are none, and no answer where they are neither.
 *
 * <p>Counting is the meaning of the question, so it stands for the answer here; that the answer
 * holds past the box is the invariant {@link TwoIntegerConstraints} states, which a box cannot
 * show.
 */
class TwoIntegerConstraintsAnswerAsEnumerationDoesTest {

    private static final int BOX = 7;
    private static final List<Rel> RELS = List.of(Rel.LE, Rel.LT, Rel.GE, Rel.GT, Rel.EQ);

    @Test
    void everySystemOfTheSampleIsAnsweredAsCountingSaysOnBothNumbers() {
        Random random = new Random(3320);
        int runs = 0;
        int nothing = 0;
        int unknown = 0;
        for (int round = 0; round < 4000; round++) {
            List<Constraint<String>> system = boxed();
            int more = 1 + random.nextInt(4);
            for (int i = 0; i < more; i++) {
                system.add(constraint(random.nextInt(9) - 4, random.nextInt(9) - 4,
                        random.nextInt(21) - 10, RELS.get(random.nextInt(RELS.size()))));
            }
            for (String axis : List.of("x", "y")) {
                Shadow said = TwoIntegerConstraints.of("x", "y", system).shadowOn(axis);
                Shadow counted = counted(system, axis);
                assertEquals(counted, said, () -> axis + " of " + system);
                runs += counted instanceof Shadow.Run ? 1 : 0;
                nothing += counted instanceof Shadow.Nothing ? 1 : 0;
                unknown += counted instanceof Shadow.Unknown ? 1 : 0;
            }
        }
        // The sample holds each kind of answer, so that agreeing is not agreeing on one.
        assertEquals(true, runs > 500 && nothing > 500 && unknown > 50,
                runs + " runs, " + nothing + " empty, " + unknown + " neither");
    }

    @Test
    void aConstraintAndItsMultiplesAreOneConstraint() {
        Shadow once = TwoIntegerConstraints.of("x", "y", withBox(constraint(1, -2, 0, Rel.LT)))
                .shadowOn("x");
        assertEquals(once, TwoIntegerConstraints.of("x", "y",
                withBox(constraint(2, -4, 0, Rel.LT))).shadowOn("x"));
        assertEquals(once, TwoIntegerConstraints.of("x", "y", withBox(new Constraint<>(
                new LinearForm<>(ExactRatio.ZERO, Map.of("x", ExactRatio.of(BigInteger.ONE,
                        BigInteger.TWO), "y", ExactRatio.ONE.negated())), Rel.LT)))
                .shadowOn("x"));
    }

    @Test
    void aConstraintHoldingANumberApartOrNamingAThirdIsNoConstraintHere() {
        assertNull(TwoIntegerConstraints.of("x", "y", List.of(constraint(1, 0, 3, Rel.NE))));
        assertNull(TwoIntegerConstraints.of("x", "y", List.of(new Constraint<>(
                new LinearForm<>(ExactRatio.ZERO, Map.of("z", ExactRatio.ONE)), Rel.GE))));
    }

    /** What counting the whole numbers of the box says of {@code axis}. */
    private static Shadow counted(List<Constraint<String>> system, String axis) {
        List<Integer> having = new ArrayList<>();
        for (int value = -BOX; value <= BOX; value++) {
            for (int other = -BOX; other <= BOX; other++) {
                int x = axis.equals("x") ? value : other;
                int y = axis.equals("x") ? other : value;
                if (system.stream().allMatch(each -> holds(each, x, y))) {
                    having.add(value);
                    break;
                }
            }
        }
        if (having.isEmpty()) {
            return new Shadow.Nothing();
        }
        int least = having.getFirst();
        int greatest = having.getLast();
        return having.size() == greatest - least + 1
                ? new Shadow.Run(BigInteger.valueOf(least), BigInteger.valueOf(greatest))
                : new Shadow.Unknown();
    }

    private static boolean holds(Constraint<String> each, int x, int y) {
        ExactRatio sum = each.form().constant();
        sum = sum.plus(ExactRatio.of(x).times(coefficient(each, "x")).orNull()).orNull();
        sum = sum.plus(ExactRatio.of(y).times(coefficient(each, "y")).orNull()).orNull();
        return each.rel().holds(sum.signum());
    }

    private static ExactRatio coefficient(Constraint<String> each, String of) {
        ExactRatio found = each.form().coefs().get(of);
        return found == null ? ExactRatio.ZERO : found;
    }

    private static Constraint<String> constraint(int a, int b, int k, Rel rel) {
        Map<String, ExactRatio> coefs = new HashMap<>();
        if (a != 0) {
            coefs.put("x", ExactRatio.of(a));
        }
        if (b != 0) {
            coefs.put("y", ExactRatio.of(b));
        }
        return new Constraint<>(new LinearForm<>(ExactRatio.of(k), coefs), rel);
    }

    /** The box, as four constraints. */
    private static List<Constraint<String>> boxed() {
        List<Constraint<String>> box = new ArrayList<>();
        box.add(constraint(1, 0, BOX, Rel.GE));
        box.add(constraint(1, 0, -BOX, Rel.LE));
        box.add(constraint(0, 1, BOX, Rel.GE));
        box.add(constraint(0, 1, -BOX, Rel.LE));
        return box;
    }

    private static List<Constraint<String>> withBox(Constraint<String> one) {
        List<Constraint<String>> all = boxed();
        all.add(one);
        return all;
    }
}
