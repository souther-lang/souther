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
import static org.junit.jupiter.api.Assertions.assertTrue;

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

    /** {@code a·x + b·y + k rel 0}, in the whole numbers counting is done in. */
    private record Row(int a, int b, int k, Rel rel) {

        boolean holdsAt(int x, int y) {
            return rel.holds(Integer.signum(a * x + b * y + k));
        }

        Constraint<String> asAConstraint() {
            Map<String, ExactRatio> coefs = new HashMap<>();
            if (a != 0) {
                coefs.put("x", ExactRatio.of(a));
            }
            if (b != 0) {
                coefs.put("y", ExactRatio.of(b));
            }
            return new Constraint<>(new LinearForm<>(ExactRatio.of(k), coefs), rel);
        }
    }

    @Test
    void everySystemOfTheSampleIsAnsweredAsCountingSaysOnBothNumbers() {
        Random random = new Random(3320);
        int runs = 0;
        int nothing = 0;
        int unknown = 0;
        for (int round = 0; round < 4000; round++) {
            List<Row> system = boxed();
            int more = 1 + random.nextInt(4);
            for (int i = 0; i < more; i++) {
                system.add(new Row(random.nextInt(9) - 4, random.nextInt(9) - 4,
                        random.nextInt(21) - 10, RELS.get(random.nextInt(RELS.size()))));
            }
            TwoIntegerConstraints<String> held = TwoIntegerConstraints.of("x", "y",
                    system.stream().map(Row::asAConstraint).toList());
            for (String axis : List.of("x", "y")) {
                Shadow counted = counted(system, axis);
                assertEquals(counted, held.shadowOn(axis), () -> axis + " of " + system);
                runs += counted instanceof Shadow.Run ? 1 : 0;
                nothing += counted instanceof Shadow.Nothing ? 1 : 0;
                unknown += counted instanceof Shadow.NotARun ? 1 : 0;
            }
        }
        // The sample holds each kind of answer, so that agreeing is not agreeing on one.
        assertTrue(runs > 500 && nothing > 500 && unknown > 50,
                runs + " runs, " + nothing + " empty, " + unknown + " neither");
    }

    @Test
    void aConstraintAndItsMultiplesAreOneConstraint() {
        Shadow once = TwoIntegerConstraints.of("x", "y", withBox(new Row(1, -2, 0, Rel.LT)))
                .shadowOn("x");
        assertEquals(once, TwoIntegerConstraints.of("x", "y",
                withBox(new Row(2, -4, 0, Rel.LT))).shadowOn("x"));
        List<Constraint<String>> halved = withBox(new Row(0, 0, 0, Rel.EQ));
        halved.removeLast();
        halved.add(new Constraint<>(new LinearForm<>(ExactRatio.ZERO, Map.of("x",
                ExactRatio.of(BigInteger.ONE, BigInteger.TWO), "y", ExactRatio.ONE.negated())),
                Rel.LT));
        assertEquals(once, TwoIntegerConstraints.of("x", "y", halved).shadowOn("x"));
    }

    @Test
    void aConstraintHoldingANumberApartOrNamingAThirdIsNoConstraintHere() {
        assertNull(TwoIntegerConstraints.of("x", "y",
                List.of(new Row(1, 0, 3, Rel.NE).asAConstraint())));
        assertNull(TwoIntegerConstraints.of("x", "y", List.of(new Constraint<>(
                new LinearForm<>(ExactRatio.ZERO, Map.of("z", ExactRatio.ONE)), Rel.GE))));
    }

    /**
     * Thirty-one lower and thirty-one upper bounds of {@code y} that round by 64 and by 63 leave
     * 4032 classes of {@code x} each asked 961 pairs: more steps than a question is worked out in.
     * Every {@code x} from nought to a million has a {@code y} here, which is what a question
     * worked out would say; it is not worked out, and is no answer.
     */
    @Test
    void aQuestionOfMoreStepsThanAreWorkedOutIsNoAnswer() {
        List<Constraint<String>> system = new ArrayList<>();
        for (int i = 0; i < 31; i++) {
            system.add(new Row(1, -64, -i, Rel.LE).asAConstraint());
            system.add(new Row(-1, 63, -10_000_000 - i, Rel.LE).asAConstraint());
        }
        system.add(new Row(1, 0, 0, Rel.GE).asAConstraint());
        system.add(new Row(1, 0, -1_000_000, Rel.LE).asAConstraint());
        assertEquals(new Shadow.OverTheLimit(),
                TwoIntegerConstraints.of("x", "y", system).shadowOn("x"));
    }

    /** Over the limit is not worked out and is said so; one step under it is. */
    @Test
    void theLimitOnClassesIsAtFortyNinetySixAndNotBeyond() {
        // y at least x over 4096, and at most x: 4096 classes, then 4097.
        assertEquals(false, TwoIntegerConstraints.of("x", "y", List.of(
                new Row(1, -4096, 0, Rel.LE).asAConstraint(),
                new Row(-1, 1, 0, Rel.LE).asAConstraint(),
                new Row(1, 0, 0, Rel.GE).asAConstraint(),
                new Row(1, 0, -9999, Rel.LE).asAConstraint()))
                .shadowOn("x") instanceof Shadow.OverTheLimit);
        assertEquals(new Shadow.OverTheLimit(), TwoIntegerConstraints.of("x", "y", List.of(
                new Row(1, -4097, 0, Rel.LE).asAConstraint(),
                new Row(-1, 1, 0, Rel.LE).asAConstraint(),
                new Row(1, 0, 0, Rel.GE).asAConstraint(),
                new Row(1, 0, -9999, Rel.LE).asAConstraint())).shadowOn("x"));
    }

    @Test
    void theLimitOnConstraintsIsSixtyFourAndNotBeyond() {
        List<Constraint<String>> constraints = new ArrayList<>();
        for (int i = 0; i < 64; i++) {
            constraints.add(new Row(1, 0, -i, Rel.LE).asAConstraint());
        }
        assertEquals(true, TwoIntegerConstraints.of("x", "y", constraints) != null);
        constraints.add(new Row(1, 0, -64, Rel.LE).asAConstraint());
        assertNull(TwoIntegerConstraints.of("x", "y", constraints));
    }

    /** No bound on either number, and a bound on one side only. */
    @Test
    void aNumberWithNoBoundHasPartnersWithoutAnEnd() {
        assertEquals(new Shadow.Run(null, null),
                TwoIntegerConstraints.of("x", "y", List.<Constraint<String>>of()).shadowOn("x"));
        // y at least x, x at least nought: x from nought up, whatever y is.
        TwoIntegerConstraints<String> above = TwoIntegerConstraints.of("x", "y", List.of(
                new Row(-1, 1, 0, Rel.GE).asAConstraint(),
                new Row(1, 0, 0, Rel.GE).asAConstraint()));
        assertEquals(new Shadow.Run(BigInteger.ZERO, null), above.shadowOn("x"));
        assertEquals(new Shadow.Run(BigInteger.ZERO, null), above.shadowOn("y"));
    }

    /**
     * A coefficient too fine to hold as a whole numerator over a whole denominator is no
     * constraint, and is not taken for another: a power of two as far below nought as exponents go.
     */
    @Test
    void aCoefficientTooFineToHoldIsNotTakenForAnother() {
        ExactRatio tiny = new ExactRatio(BigInteger.ONE, BigInteger.ONE, Long.MIN_VALUE, 0);
        assertNull(TwoIntegerConstraints.of("x", "y", List.of(new Constraint<>(
                new LinearForm<>(ExactRatio.ZERO, Map.of("x", ExactRatio.ONE, "y", tiny)),
                Rel.LE))));
    }

    /** What counting the whole numbers of the box says of {@code axis}. */
    private static Shadow counted(List<Row> system, String axis) {
        List<Integer> having = new ArrayList<>();
        for (int value = -BOX; value <= BOX; value++) {
            for (int other = -BOX; other <= BOX; other++) {
                int x = axis.equals("x") ? value : other;
                int y = axis.equals("x") ? other : value;
                if (system.stream().allMatch(each -> each.holdsAt(x, y))) {
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
                : new Shadow.NotARun();
    }

    /** The box, as four constraints. */
    private static List<Row> boxed() {
        List<Row> box = new ArrayList<>();
        box.add(new Row(1, 0, BOX, Rel.GE));
        box.add(new Row(1, 0, -BOX, Rel.LE));
        box.add(new Row(0, 1, BOX, Rel.GE));
        box.add(new Row(0, 1, -BOX, Rel.LE));
        return box;
    }

    private static List<Constraint<String>> withBox(Row one) {
        List<Row> all = boxed();
        all.add(one);
        return new ArrayList<>(all.stream().map(Row::asAConstraint).toList());
    }
}
